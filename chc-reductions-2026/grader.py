"""
Автоматическая проверка решения.

    python grader.py             # проверяет main.py
    python grader.py path/to.py  # проверяет другой файл

Для каждой задачи:
  1. task_N_chc() решается Spacer'ом — ответ должен быть sat (свойство доказано);
  2. task_N_check(model, ...) вызывается на тестах:
       * реальные исполнения функции — модель должна их допускать (True);
       * исполнения, нарушающие свойство, — модель должна их отвергать (False);
     check должен вычисляться упрощением модели: без решателя, без запуска самой
     функции.
  В задаче 4 check(a, b) — значение слабейшего предусловия отсутствия исключения;
  оно сверяется с реальным поведением функции на входах.
"""
import contextlib
import importlib.util
import os
import sys
import traceback

from z3 import (
    BoolSort,
    BoolVal,
    Solver,
    SolverFor,
    is_bool,
    is_false,
    is_true,
    sat,
    simplify,
    substitute_funs,
    unsat,
)


def evaluate(expr):
    value = simplify(expr)
    return True if is_true(value) else False if is_false(value) else None

sys.setrecursionlimit(20_000)
TIMEOUT_MS = 10_000


class Fail(Exception):
    pass


class Forbidden(Exception):
    pass


def horn(chc):
    s = SolverFor("HORN")
    s.set("engine", "spacer")
    s.set("timeout", TIMEOUT_MS)
    s.set("xform.inline_eager", False)
    s.set("xform.inline_linear", False)
    s.set("xform.slice", False)
    s.add(chc)
    status = s.check()
    return status, (s.model() if status == sat else None)


class ConstModel:
    def __init__(self, model, value):
        self.subst = [(d, BoolVal(value)) for d in model.decls()
                      if d.arity() > 0 and d.range() == BoolSort()]

    def eval(self, expr, model_completion=False):
        return substitute_funs(expr, *self.subst)

    evaluate = eval


@contextlib.contextmanager
def no_cheating(module, program):
    def forbid(what):
        def f(*args, **kwargs):
            raise Forbidden(f"в check нельзя использовать {what}")
        return f

    saved_check, saved_prog = Solver.check, getattr(module, program)
    Solver.check = forbid("решатель")
    setattr(module, program, forbid(f"функцию {program}"))
    try:
        yield
    finally:
        Solver.check = saved_check
        setattr(module, program, saved_prog)


def solve_system(chc):
    if not isinstance(chc, (list, tuple)) or not chc:
        raise Fail("система CHC не задана")
    if not all(is_bool(c) for c in chc):
        raise Fail("task_chc должна возвращать список формул")
    return horn(list(chc))


def grade(module, n, program, cases):
    check_fn = getattr(module, f"task_{n}_check")
    status, model = solve_system(getattr(module, f"task_{n}_chc")())
    if status == unsat:
        raise Fail("решатель нашёл контрпример: свойство не доказано (или правила неверны)")
    if status != sat:
        raise Fail("решатель не справился за отведённое время")

    def call(m, args):
        with no_cheating(module, program):
            try:
                return check_fn(m, *args)
            except Forbidden as e:
                raise Fail(str(e))

    for args, _ in cases:
        if call(ConstModel(model, True), args) == call(ConstModel(model, False), args):
            raise Fail(f"check{args} судит не по модели: ответ не меняется, когда все "
                       f"предикаты подменяются на True или на False")
    for args, expected in cases:
        got = call(model, args)
        if got is None:
            raise Fail(f"check{args} не упростился до константы: в модели кванторы "
                       f"или предикат не вычисляется на конкретных данных")
        if got is not expected:
            raise Fail(f"check{args} = {got}, ожидалось {expected}")


def split(positives, negatives):
    return [(c, True) for c in positives] + [(c, False) for c in negatives]


##################################################
# Тесты


def grade_task_1(T):
    positives = [(x, T.double(x)) for x in [-3, -1, 0, 1, 2, 5, 10]]
    negatives = [(0, 1), (3, 5), (3, 7), (5, 0), (10, -20)]
    grade(T, 1, "double", split(positives, negatives))


def grade_task_2(T):
    positives = [(m, n, T.ack(m, n)) for m, n in [(0, 0), (0, 7), (1, 0), (1, 3), (2, 2), (3, 1), (3, 3)]]
    negatives = [(0, 5, 4), (1, 3, 0), (2, 10, 9), (3, 4, -1)]
    grade(T, 2, "ack", split(positives, negatives))


def grade_task_3(T):
    cases = [([3, 1, 4, 1], 1), ([3, 1, 4], 7), ([], 5), ([2, 2], 2), ([5, 6, 7], 7)]
    positives = [(arr, v, T.search_in_array(arr, v)) for arr, v in cases]
    negatives = [([3, 1, 4], 1, 0), ([3, 1, 4], 7, 3), ([], 5, 0), ([2, 2], 2, -2), ([5, 6, 7], 7, 1)]
    grade(T, 3, "search_in_array", split(positives, negatives))


def raises(T, a, b):
    try:
        T.recursive_simple(a, b)
        return False
    except Exception:
        return True


def grade_task_4(T):
    inputs = [(x, y) for x in range(-3, 45) for y in range(-3, 45)]
    inputs += [(x, x + d) for x in (500, 5000) for d in (-300, -2, -1, 0, 1, 2, 300)]
    grade(T, 4, "recursive_simple", [((a, b), not raises(T, a, b)) for a, b in inputs])


##################################################


def load(path):
    spec = importlib.util.spec_from_file_location("solution", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(name, points, fn, *args):
    try:
        fn(*args)
        print(f"[+] {name}: {points}/{points}")
        return points
    except Fail as e:
        print(f"[-] {name}: 0/{points}\n      {e}")
    except Exception:
        print(f"[-] {name}: 0/{points}\n      ошибка при выполнении:")
        print("      " + traceback.format_exc().strip().replace("\n", "\n      "))
    return 0


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "main.py")
    m = load(path)
    total = 0
    total += run("Задача 1 (цикл)", 1, grade_task_1, m)
    total += run("Задача 2 (ack)", 2, grade_task_2, m)
    total += run("Задача 3 (массив)", 3, grade_task_3, m)
    total += run("Задача 4 (исключения и предусловие)", 4, grade_task_4, m)
    print(f"\nИтого: {total}/10")


if __name__ == "__main__":
    main()
