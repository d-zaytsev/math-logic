import abc
import os
from itertools import combinations

from z3 import *


class EqTheorySolver(abc.ABC):
    """
    Решатель теории с равенством: принимает конъюнкцию литералов вида `s = t` и `s != t`
    """

    @abc.abstractmethod
    def add_equal(self, a, b):
        raise NotImplementedError()

    @abc.abstractmethod
    def add_distinct(self, a, b):
        raise NotImplementedError()

    def add_literal(self, literal):
        negated = False
        while is_not(literal):
            negated = not negated
            literal = literal.arg(0)
        if is_eq(literal) or (is_distinct(literal) and literal.num_args() == 2):
            if is_eq(literal) != negated:
                self.add_equal(literal.arg(0), literal.arg(1))
            else:
                self.add_distinct(literal.arg(0), literal.arg(1))
        elif is_distinct(literal) and not negated:
            for a, b in combinations(literal.children(), 2):
                self.add_distinct(a, b)
        else:
            raise NotImplementedError(literal)

    def add(self, *formulas):
        for formula in formulas:
            self.add_literal(formula)


def check_formulas(SolverConstr, formulas, expected):
    solver = SolverConstr()
    solver.add(*formulas)
    result = solver.check()
    assert result == expected, f"{formulas}: expected {expected}, got {result}"


def linearize(fs):
    """Превращает формулу в конъюнкцию литералов, оставляя из каждой дизъюнкции только первый дизъюнкт"""
    for f in fs:
        if is_and(f):
            yield from linearize(f.children())
        elif is_or(f):
            yield from linearize([f.arg(0)])
        else:
            yield f


def Solver_test_file(SolverConstr, preprocess, filename):
    print(filename)
    fs = list(preprocess(parse_smt2_file(filename)))
    gold_solver = Solver()
    gold_solver.add(*fs)
    desired_result = gold_solver.check()
    solver = SolverConstr()
    solver.add(*fs)
    result = solver.check()
    assert result == desired_result, (
        f"{filename}: expected {desired_result}, got {result}"
    )


def Solver_test_files(SolverConstr, preprocess, benchmark_dir):
    for base, _, filenames in sorted(os.walk(benchmark_dir)):
        for filename in sorted(filenames):
            Solver_test_file(SolverConstr, preprocess, os.path.join(base, filename))
