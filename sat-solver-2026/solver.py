import sys
from threading import Event

from utils import SATSolverResult, lit_to_dimacs, load_formula


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.vars_count = self.formula.num_vars
        self.literals_count = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.literals = [0] * self.literals_count

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated_ref = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess()

    def preprocess(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses: list[list[int]] = []
        self.units = []
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.append(lits.pop())
            else:
                self.clauses.append(list(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int):
        """Сделать ℓ истинным на текущем уровне."""
        self.literals[lit] = 1
        self.literals[lit ^ 1] = -1
        self.trail.append(lit)

    def decide(self, lit: int):
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int):
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return
        values, trail = self.literals, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
        del trail[start:]
        del self.control[level:]
        self.propagated_ref = start

    def save_model(self):
        values = self.literals
        self.model = [
            lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
            for v in range(1, self.vars_count + 1)
        ]

    def build_watches(self):
        num_lits = self.formula.num_lits
        self.binary = [[] for _ in range(num_lits)]
        self.watches = [[] for _ in range(num_lits)]
        for c in self.clauses:
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])

    def propagate(self) -> bool:
        """
        UnitPropagate: распространить литералы trail[propagated:].
        Возвращает True, если найден конфликт (все литералы дизъюнкта ложны).
        """
        occurrences: list[list] = [[] for _ in range(self.formula.num_lits)]
        for c in self.clauses:
            for lit in c:
                occurrences[lit].append(c)
        
        while self.propagated_ref < len(self.trail):
            false_lit = self.trail[self.propagated_ref] ^ 1
            self.propagated_ref += 1

            for c in occurrences[false_lit]:
                unassigned = []
                for lit in c:
                    if self.literals[lit] > 0:
                        break
                    if self.literals[lit] == 0:
                        unassigned.append(lit)
                else:
                    if len(unassigned) == 0:
                        return True
                    if len(unassigned) == 1:
                        self.assign(unassigned[0])
        return False

    def choose_literal(self) -> int | None:
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        for v in range(1, self.vars_count + 1):
            if self.literals[2 * v] == 0:
                return 2 * v + 1
        return None

    def solve(self) -> SATSolverResult:
        if self.has_empty_clause:
            return SATSolverResult.UNSAT

        for lit in self.units:
            if self.literals[lit] < 0:
                return SATSolverResult.UNSAT
            if self.literals[lit] == 0:
                self.assign(lit)

        while True:
            if self.sigkill.is_set():
                return SATSolverResult.UNKNOWN

            if self.propagate():  # backtrack
                if self.level() == 0:
                    return SATSolverResult.UNSAT

                lit = self.decision(self.level())
                self.backtrack(self.level() - 1)
                self.assign(lit ^ 1)
                continue

            lit = self.choose_literal()

            if lit is None:  # find solution!!!
                return SATSolverResult.SAT
            else:
                self.decide(lit)


if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
