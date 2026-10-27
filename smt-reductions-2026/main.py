from time import perf_counter

from z3 import *


def model2formula(model):
    return And(*[v() == model[v()] for v in model])


# Пример: решение теоремы Ферма (теория NIA)
def ferma_theorem(easy=True):  # NIA
    x, y, z = Ints("x y z")
    s = Solver()
    for v in [x, y, z]:
        s.add(v > 0)
    if easy:
        s.add(x < y)
        s.add(y < z)
        s.add(x * x + y * y == z * z)
    else:
        s.add(x * x * x + y * y * y == z * z * z)  # should be unsat, but diverges
    print(s.to_smt2())
    while s.check() == sat:
        model = s.model()
        print(model[x], model[y], model[z])
        s.add(Not(model2formula(model)))


INT_SIZE = 32


def abs_ex():  # BV
    x, y = BitVecs("x y", INT_SIZE)
    s = Solver()
    s.add(y == If(x >= 0, x, -x))
    s.add(Not(y >= 0))
    s.check()
    print(s.model())


# Пример: факторизация чисел (теория BV)
def factor(out, nia=False, long=False):  # BV
    long = not nia and long
    x, y, n = Ints("x y n") if nia else BitVecs("x y n", INT_SIZE)
    s = Solver()
    s.add(n == out)
    if long:
        xe, ye, ne = map(lambda v: ZeroExt(INT_SIZE, v), [x, y, n])
        s.add(ne == xe * ye)
    else:
        s.add(n == x * y)
    s.add(x <= y)
    for v in [x, y]:
        s.add(v > 1)
        s.add(v < n)
    t = perf_counter()
    s.check()
    print("Estimated time:", perf_counter() - t)
    # print(s.to_smt2())
    model = s.model()
    xv = model[x]
    yv = model[y]
    xy = xv.as_long() * yv.as_long()
    print(f"{xv} * {yv} = {xy}", end="")
    if not nia:
        print(f" ?= {xy % (1 << INT_SIZE)}")
    else:
        print()


def is_power_of_two():
    """
    TODO: 1 point
    Докажите при помощи SMT-решателя, что `(x != 0) && (x & (x - 1)) == 0` - это код,
    возвращающий истинное значение
    тогда и только тогда, когда битвектор x является степенью двойки.
    """

    for i in range(1, 20):
        x = BitVec("x", i)
        s = Solver()

        s.add(Xor(And(x != 0, (x & (x - 1)) == 0), Or([x == 2**k for k in range(i)])))
        attempt = s.check()

        assert attempt == unsat, f"утверждение не доказано для SIZE = {i}"


def bithack():
    def is_identity(a: int, b: int, BIT_WIDTH: int) -> bool:
        mask = (1 << BIT_WIDTH) - 1
        return all(
            (((x + a) ^ b) - a) & mask == (((x - a) ^ b) + a) & mask
            for x in range(1 << BIT_WIDTH)
        )

    def attempt(BIT_WIDTH: int) -> set[tuple[int, int]]:
        """
        TODO: 1 point
        J. H. Quick noticed that ((x + 2) ⊕ 3) - 2 = ((x - 2) ⊕ 3) + 2 for all x.
        Find all constants a and b such that ((x + a) ⊕ b) - a = ((x - a) ⊕ b) + a is an identity.

        :param BIT_WIDTH: width of bit vectors a, b, x
        :return set of pairs of `a` and `b`
        """
        a, b, x = BitVecs("a b x", BIT_WIDTH)
        s = Solver()
        res: set[tuple[int, int]] = set()
        f = (((x + a) ^ b) - a) == (((x - a) ^ b) + a)
        
        s.add(ForAll([x], f))
        while s.check() == sat:
            model = s.model()
            res.add((model[a].as_long(), model[b].as_long()))
            s.add(Not(model2formula(model)))

        return res

    results = {width: attempt(width) for width in range(2, 6)}
    for width, pairs in results.items():
        for a, b in pairs:
            assert 0 <= a < 1 << width and 0 <= b < 1 << width, (
                f"({a}, {b}) does not fit into {width} bits"
            )
            assert is_identity(a, b, width), (
                f"not an identity for a = {a}, b = {b}, BIT_WIDTH = {width}"
            )
    assert results[2] == {
        (3, 3),
        (0, 0),
        (1, 1),
        (2, 0),
        (2, 2),
        (2, 3),
        (0, 3),
        (0, 1),
        (0, 2),
        (1, 0),
        (3, 0),
        (3, 1),
        (2, 1),
        (1, 2),
        (1, 3),
        (3, 2),
    }
    assert results[3] == {
        (4, 0),
        (3, 4),
        (4, 3),
        (3, 1),
        (5, 4),
        (4, 6),
        (5, 1),
        (0, 2),
        (0, 5),
        (2, 2),
        (1, 0),
        (2, 5),
        (7, 4),
        (6, 2),
        (7, 1),
        (6, 5),
        (4, 2),
        (3, 0),
        (4, 5),
        (5, 0),
        (0, 1),
        (0, 7),
        (2, 4),
        (0, 4),
        (2, 1),
        (2, 7),
        (1, 5),
        (6, 1),
        (7, 0),
        (6, 4),
        (6, 7),
        (4, 1),
        (4, 7),
        (3, 5),
        (4, 4),
        (5, 5),
        (0, 0),
        (1, 1),
        (0, 3),
        (2, 0),
        (1, 4),
        (0, 6),
        (2, 3),
        (2, 6),
        (6, 0),
        (6, 6),
        (7, 5),
        (6, 3),
    }
    assert len(results[4]) == 128
    assert len(results[5]) == 320


def queens():
    def is_ok(size, xs):
        return (
            len(xs) == size
            and set(xs) == set(range(1, size + 1))
            and len({x - i for i, x in enumerate(xs)}) == size
            and len({x + i for i, x in enumerate(xs)}) == size
        )

    def attempt(SIZE: int) -> list[int]:
        """
        TODO: 3 points
        Решите задачу о расстановке ферзей, сведя задачу в линейную арифметику.
        На шахматной доске SIZE x SIZE нужно расставить SIZE ферзей так, чтобы 
        никакие два из них не били друг друга,
        то есть не стояли в одной строке, в одном столбце или на одной диагонали.
        Запишите эти условия формулой линейной целочисленной арифметики над
        целочисленными переменными,
        найдите её модель при помощи решателя и восстановите по модели расстановку.
        :param SIZE: число ферзей >= 8
        :return: список из SIZE целых чисел (именно `int`, а не выражений z3) от 1 до SIZE:
            если по индексу i расположено число j в списке, тогда в строке i+1 и в столбце j стоит ферзь
            Пример: [4, 2, 8, 6, 1, 3, 5, 7]
        """
        s = SolverFor("QF_LIA")
        vars = " ".join(f"q_i{i}" for i in range(SIZE))
        q_is = Ints(vars)
        
        for q_i in q_is:
            s.add(And(q_i >= 1, q_i <= SIZE))

        for i in range(SIZE-1):
            s.add(q_is[i] != q_is[i+1]) 

        for i in range(SIZE):
            for j in range(i + 1, SIZE):
                s.add(q_is[i] != q_is[j])
                s.add(i - j != q_is[i] - q_is[j])
                s.add(abs(j - i) != Abs(q_is[i] - q_is[j]))

        s.check()
        model = s.model()
        
        return [model[q].as_long() for q in q_is]

    for s in range(8, 40):
        xs = attempt(s)
        print(xs)
        assert is_ok(s, xs), f"{xs} - некорректная расстановка {s} ферзей"


# Пример: проверка сортированности массива (теория A)
def sortedness():
    array_sort = ArraySort(IntSort(), IntSort())
    sorted = RecFunction("sorted", array_sort, BoolSort())
    arr = Const("arr", array_sort)
    i, j = Ints("i j")
    RecAddDefinition(sorted, arr, ForAll([i, j], Implies(i <= j, arr[i] <= arr[j])))
    a = Const("a", array_sort)
    x, y, z = Ints("x y z")
    solver = Solver()
    query = [
        0 <= x,
        0 <= y,
        0 <= z,
        x <= 10,
        y <= 10,
        z <= 10,
        sorted(a),
        y <= z,
        a[x] == a[z],
        a[x] != a[y],
    ]
    solver.add(query)
    solver.push()
    solver.add(x <= y)
    print(solver.check())
    if solver.check() == sat:
        print(solver.model())
    solver.pop()
    solver.push()
    solver.add(x - 1 <= y)
    print(solver.check())
    if solver.check() == sat:
        print(solver.model())


def array_theory_proof():
    r"""
    TODO: 2 points
    Предъявите литерал (не произвольную формулу!) F и список из n литералов Fs = [F1, ..., Fn] 
    в теории массивов над линейной целочисленной арифметикой,
    такие что:
    - n >= 2
    - |= F -> (F1 \/ ... \/ Fn)
    - для всех 1 <= i <= n не верно, что |= F -> Fi
    Эти проверки уже закодированы для вас в функции check, вам нужно только придумать и записать литералы F и Fs.
    Замечание: это упражнение фактически показывает, что теория массивов невыпукла
    """

    def is_literal(f):
        def has_formula_inside(t):
            return any(is_bool(c) or has_formula_inside(c) for c in t.children())

        if is_not(f):
            f = f.arg(0)
        return (
            is_bool(f)
            and is_app(f)
            and not has_formula_inside(f)
            and not (is_distinct(f) and f.num_args() > 2)
        )

    def check(F, Fs):
        assert len(Fs) >= 2
        for lit in [F, *Fs]:
            assert is_literal(lit), f"{lit} - не литерал"
        solver = SolverFor("QF_AUFLIA")
        solver.push()
        solver.add(Not(Implies(F, Or(Fs))))
        assert solver.check() == unsat
        solver.pop()
        for Fi in Fs:
            solver.push()
            solver.add(Not(Implies(F, Fi)))
            assert solver.check() == sat
            solver.pop()

    F = None
    Fs = []
    check(F, Fs)


# Пример: решение уравнений на типами (теория EUF)
def subtyping():
    def card_at_most(Sort, card):
        cs = [Const(c, Sort) for c in range(card)]
        x = Const(card, Sort)
        return Exists(cs, ForAll(x, Or([x == c for c in cs])))

    Type = DeclareSort("Type")
    subtype = Function("subtype", Type, Type, BoolSort())
    exception = Const("exception", Type)
    Object = Const("Object", Type)

    x, y, z, v = Consts("x y z v", Type)
    axioms = [
        subtype(x, x),
        Implies(And(subtype(x, y), subtype(y, z)), subtype(x, z)),
        Implies(And(subtype(x, y), subtype(y, x)), x == y),
        subtype(x, Object),
        subtype(exception, x),
    ]
    solver = Solver()
    solver.add([ForAll([x, y, z, v], ax) for ax in axioms])
    solver.add(card_at_most(Type, 5))
    # a, b, c, d = Consts("a b c d", Type)
    # solver.add([Exists([a, b, c], ForAll(d, Or(d == a, d == b, d == c)))])

    s, t = Consts("s t", Type)
    solver.add(Not(subtype(s, t)))
    solver.add(Not(subtype(t, s)))
    print(solver.check())
    print("Interpretation for Type:")
    print(solver.model()[Type])
    print("Model:")
    print(solver.model())


def groups():
    """
    TODO: 3 points
    Определите группу в теории неинтерпретированных функций (определите сорт, константы, функции, задайте аксиомы)
    https://ru.wikipedia.org/wiki/%D0%93%D1%80%D1%83%D0%BF%D0%BF%D0%B0_(%D0%BC%D0%B0%D1%82%D0%B5%D0%BC%D0%B0%D1%82%D0%B8%D0%BA%D0%B0)#%D0%9E%D0%BF%D1%80%D0%B5%D0%B4%D0%B5%D0%BB%D0%B5%D0%BD%D0%B8%D0%B5
    Затем докажите при помощи SMT-решателя, следующие теоремы:
    - обратный элемент для произведения - это произведение обратных элементов, взятых в обратном порядке
    - если обратные для двух элементов равны, то равны сами эти элементы
    - обратный элемент для обратного это сам элемент
    - обратный элемент для единицы - единица

    Сами доказательства уже закодированы для вас в функции check, вам нужно только записать формулы:
    аксиомы группы в список axioms и четыре теоремы (в том же порядке, что и выше) в список theorems.
    Замечание: когда решатель `solver` (см. verdict) вернул unsat, можно посмотреть на произведённое им доказательство: print(solver.proof().sexpr())
    (Для этого в начало решения вставьте `set_param(proof=True)`)
    """

    def check(axioms, theorems):
        assert len(axioms) > 0
        assert len(theorems) == 4

        def verdict(formulas):
            solver = Solver()
            solver.set("rlimit", 5000000)
            solver.add(formulas)
            return solver.check()

        assert verdict(axioms) != unsat, "аксиомы противоречивы"
        for theorem in theorems:
            assert verdict([Not(theorem)]) != unsat, (
                f"{theorem} верно и без аксиом группы"
            )
            assert verdict([*axioms, Not(theorem)]) == unsat, (
                f"{theorem} не выведено из аксиом"
            )

    axioms = []
    theorems = []
    check(axioms, theorems)


import traceback


def run_task(task):
    try:
        print("=======================================")
        print(f"Start: {task.__name__}")
        task()
        print(f"Finish: {task.__name__}")
    except Exception as ex:
        print(f"FAILURE: {type(ex)}")
        traceback.print_exc()


if __name__ == "__main__":
    run_task(is_power_of_two)
    run_task(bithack)
    run_task(queens)
    # run_task(array_theory_proof)
    # run_task(groups)
