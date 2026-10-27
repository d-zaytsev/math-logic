from dataclasses import dataclass

from z3 import (
    And, ArraySort, Exists, FreshConst, FreshInt, IntSort, Solver, Tactic,
    TryFor, Xor, Z3_ARRAY_SORT, Z3_OP_DISTINCT, Z3_OP_EQ, Z3_OP_UNINTERPRETED,
    is_bool, is_quantifier, sat, unsat,
)


TIMEOUT_MS = 5000


@dataclass(frozen=True)
class Exercise:
    number: int
    points: int
    arguments: tuple
    expected: object
    arrays: tuple = ()
    model_cases: tuple = ()


def exercises():
    a, b, c, d, x, i, j, k, w = (FreshInt(name) for name in "abcdxijkw")
    A, B, C, D = (FreshConst(ArraySort(IntSort(), IntSort()), name) for name in "ABCD")

    yield Exercise(1, 1, (a, b, c), Exists(x, And(
        x >= a+2, x > b-1, 2*x >= 2*c+1, a+c <= b)))
    yield Exercise(2, 2, (a, b, c, d), Exists(x, And(
        a < 2*x, b <= x, 2*x < c, x <= d)))
    yield Exercise(3, 2, (a, b), Exists(x, And(
        a <= x, x < b, (x+1) % 2 == 0, (x-a) % 3 == 0)))

    yield Exercise(4, 1, (A, B, i, j), And(
        *[A[t] == B[t] for t in (i, i+1, j)],
        A[i] == 0, B[i+1] == 1, B[j] == 2), (A, B), (
            And(i == 0, j == 2),
            And(i == 0, j == -1),
            And(i == -3, j == -1),
        ))
    yield Exercise(5, 2, (A, B, C, i, j, k), And(
        *[And(A[t] == B[t], B[t] == C[t]) for t in (i, i+1, j, k)],
        A[i] == 0, C[j] == 1, B[k] == A[j], C[i+1] == B[i]), (A, B, C), (
            And(i == 0, j == 2, k == 3),
            And(i == 0, j == 2, k == 2),
            And(i == -3, j == 0, k == 1),
        ))
    yield Exercise(6, 2, (A, B, C, D, i, j, w), And(
        *[And(A[t] == B[t], C[t] == D[t]) for t in (i, j, w)],
        A[w] != C[w], B[w] != D[w],
        A[i] == 0, C[i] == 0, B[j] == 1, D[j] == 1), (A, B, C, D), (
            And(i == 0, j == 1, w == 2),
            And(i == 0, j == 2, w == 1),
            And(i == -3, j == 4, w == 0),
        ))


def walk(expression):
    pending = [expression]
    seen = set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        yield node
        if not is_quantifier(node):
            pending.extend(node.children())


def check_shape(result, exercise):
    if not is_bool(result):
        raise AssertionError("Верните BoolRef Z3, а не Python bool, список или модель")
    allowed = {arg.decl() for arg in exercise.arguments}
    array_symbols = {array.decl() for array in exercise.arrays}
    symbols = set()
    for node in walk(result):
        if is_quantifier(node):
            raise AssertionError("В ответе остался квантор или Lambda")
        kind = node.decl().kind()
        if kind == Z3_OP_UNINTERPRETED:
            symbols.add(node.decl())
        if kind in (Z3_OP_EQ, Z3_OP_DISTINCT) and any(
                arg.sort().kind() == Z3_ARRAY_SORT for arg in node.children()):
            raise AssertionError("В ответе осталось сравнение целых массивов")
        if node.sort().kind() == Z3_ARRAY_SORT and node.decl() not in array_symbols:
            raise AssertionError("Используйте чтения переданных массивов, без их замены")
    extra = symbols - allowed
    if extra:
        raise AssertionError(f"Посторонние символы: {sorted(map(str, extra))}")
    missing = array_symbols - symbols
    if missing:
        raise AssertionError(f"Из ответа исчезли массивы: {sorted(map(str, missing))}")


def solve(*conditions):
    solver = Solver()
    solver.set(timeout=TIMEOUT_MS)
    solver.add(*conditions)
    verdict = solver.check()
    if verdict not in (sat, unsat):
        raise AssertionError(f"Z3 не завершил проверку: {solver.reason_unknown()}")
    return solver, verdict


def check_equivalent(result, expected):
    if any(is_quantifier(node) for node in walk(expected)):
        expected = TryFor(Tactic("qe"), TIMEOUT_MS)(expected).as_expr()
        if any(is_quantifier(node) for node in walk(expected)):
            raise AssertionError("Оракул Z3 не смог устранить квантор")
    solver, verdict = solve(Xor(result, expected))
    if verdict != unsat:
        raise AssertionError(
            "Ответ не эквивалентен ожидаемым условиям.\n"
            f"  Контрпример: {solver.model()}\n"
            f"  Ответ: {result}")


def check_models(result, exercise):
    for number, conditions in enumerate(exercise.model_cases, 1):
        solver, verdict = solve(result, conditions)
        if verdict != sat:
            raise AssertionError(f"Проверка модели {number}: ожидалась выполнимая формула")
        model = solver.model()
        missing = [str(array) for array in exercise.arrays
                   if model.get_interp(array.decl()) is None]
        if missing:
            raise AssertionError(f"В модели ответа отсутствуют массивы: {missing}")


def check_answer(result, exercise):
    check_shape(result, exercise)
    check_models(result, exercise)
    check_equivalent(result, exercise.expected)


def main(module=None):
    if module is None:
        import tasks as module

    earned, total, failed = 0, 0, False
    for exercise in exercises():
        name = f"task_{exercise.number}"
        total += exercise.points
        try:
            result = getattr(module, name)(*exercise.arguments)
            check_answer(result, exercise)
            earned += exercise.points
            print(f"[OK] {name}: +{exercise.points}")
        except NotImplementedError:
            failed = True
            print(f"[FAIL] {name}: не реализовано")
        except Exception as error:
            failed = True
            print(f"[FAIL] {name}: {type(error).__name__}: {error}")
    print(f"Total points for this homework: {earned} / {total}")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
