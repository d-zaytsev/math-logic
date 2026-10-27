from z3 import And, BoolRef, Not, Or, Select


def task_1(a, b, c) -> BoolRef:
    """Устраните ∃x: x >= a+2 ∧ x > b-1 ∧ 2x >= 2c+1 ∧ a+c <= b."""
    return a + c <= b


def task_2(a, b, c, d) -> BoolRef:
    """Устраните ∃x: a < 2x ∧ b <= x ∧ 2x < c ∧ x <= d."""
    F1 = lambda y: And(a < y, 2*b - 2 < y, y < c, y < 2*d + 2, y % 2 == 0)
    
    return Or(
        F1(a+1),
        F1(a+2),
        F1(2*b - 1),
        F1(2*b)
    )



def task_3(a, b) -> BoolRef:
    """Устраните ∃x: a <= x ∧ x < b ∧ 2 | (x+1) ∧ 3 | (x-a)."""
    F1 = lambda x: And(a-1 < x, x < b, (x + 1) % 2 == 0, (x-a) % 3 == 0)
    
    return Or(*[F1(a-1+i) for i in range(1,7)])


def task_4(A, B, i, j) -> BoolRef:
    """Уберите A=B из A=B ∧ A[i]=0 ∧ B[i+1]=1 ∧ B[j]=2."""
    raise NotImplementedError()


def task_5(A, B, C, i, j, k) -> BoolRef:
    """Уберите равенства массивов:

    A=B ∧ B=C ∧ A[i]=0 ∧ C[j]=1 ∧ B[k]=A[j] ∧ C[i+1]=B[i].
    """
    raise NotImplementedError()


def task_6(A, B, C, D, i, j, w) -> BoolRef:
    """Уберите равенства и неравенства массивов:

    A=B ∧ C=D ∧ A≠C ∧ B≠D ∧ A[i]=0 ∧ C[i]=0 ∧ B[j]=1 ∧ D[j]=1.
    Используйте переданный w как общий индекс-свидетель неравенств.
    """
    raise NotImplementedError()
