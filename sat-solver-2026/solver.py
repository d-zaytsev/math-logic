import random
import sys
from threading import Event

from utils import SATSolverResult, lit_to_dimacs, load_formula


class Solver:
    literal_values: list[int]
    """values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен)"""
    num_list: int
    """Количество литералов."""
    num_vars: int
    """Количество переменных."""
    trail: list[int]
    """Означенные литералы (индексы) в порядке присваивания."""
    propagated: int
    """Индекс в списке `trail`, `trail[:propagated]` уже распространены, `trail[propagated:]` — ещё нет"""
    control: list[int]
    """`control[i]` — позиция в `trail` литерала-решения уровня `i + 1`;
    текущий уровень решения = `len(control)` (число сделанных догадок).
    Уровень решения равен числу сделанных догадок. Догадка = литерал-решение."""
    units: list[int]
    """Литералы (индексы) единичных дизъюнктов."""

    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: .
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.literal_values = [0] * num_lits

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated = 0

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

    @property
    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int):
        """Сделать ℓ истинным на текущем уровне."""
        self.literal_values[lit] = 1
        self.literal_values[lit ^ 1] = -1
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
        values, trail = self.literal_values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
        del trail[start:]
        del self.control[level:]
        self.propagated = start

    def save_model(self):
        values = self.literal_values
        self.model = [
            lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
            for v in range(1, self.num_vars + 1)
        ]

    def build_occurrences(self):
        self.occurrences = [[] for _ in range(self.formula.num_lits)]
        for c in self.clauses:
            for lit in c:
                self.occurrences[lit].append(c)

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
        # UnitPropagate
        changed = True
        while changed:
            changed = False
            for c in self.clauses:
                if any(self.literal_values[x] == 1 for x in c):
                    continue  # клоза выполнена
                if not (free := [x for x in c if self.literal_values[x] == 0]):
                    return True  # конфликт
                elif len(free) == 1:  # единичный клоз
                    self.assign(free[0])
                    changed = True

        # EliminatePureLiteral
        occurring = {
            l
            for c in self.clauses
            for l in c
            if self.literal_values[l] != 0
        }
        for l in range(self.formula.num_lits):
            if (
                self.literal_values[l] == 0
                and l ^ 1 not in occurring
            ):
                self.assign(l)

        return False

    def choose_literal(self) -> int | None:
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        for c in self.clauses:
            for l in c:
                if self.literal_values[l] == 0:
                    return l
        return None

    def solve(self) -> SATSolverResult:
        if self.has_empty_clause:
            return SATSolverResult.UNSAT
        
        for l in self.units:
            if self.literal_values[l] == -1:
                return SATSolverResult.UNSAT
            if self.literal_values[l] == 0:
                self.assign(l)

        while True:
            if self.sigkill.is_set():
                return SATSolverResult.UNKNOWN

            if self.propagate():
                # Был обнаружен конфликт
                
                if self.level == 0:  # откатываться уже некуда
                    return SATSolverResult.UNSAT

                l_decision = self.decision(self.level)
                self.backtrack(self.level - 1)
                self.decide(l_decision ^ 1)
                continue  # повторяем алгоритм

            if (lit := self.choose_literal()) is None:
                # литералы закончились
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
