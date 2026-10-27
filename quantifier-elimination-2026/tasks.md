# Элиминация кванторов

Запишите ответы как Z3-формулы в функциях `task_1`–`task_6` файла [tasks.py](tasks.py). Проверка: `python tests.py`.

В задачах 1–3 устраните квантор и запишите эквивалентную бескванторную формулу только по свободным числовым переменным исходной формулы.

В задачах 4–6 перепишите формулу в эквивыполнимую без равенств и неравенств целых массивов.

Все числовые переменные целочисленные. Массивы имеют тип $\mathbb Z\to\mathbb Z$, запись $A[i]$ означает $\operatorname{select}(A,i)$. Индексы могут совпадать, если условие явно этого не запрещает.

## 1. LIA: только нижние границы

$$
\exists x\;\bigl(
x\ge a+2
\land x>b-1
\land 2x\ge 2c+1
\land a+c\le b
\bigr).
$$

## 2. LIA: нижние и верхние границы

$$
\exists x\;\bigl(
a<2x
\land b\le x
\land 2x<c
\land x\le d
\bigr).
$$

## 3. LIA: границы и два условия делимости

$$
\exists x\;\bigl(
a\le x
\land x<b
\land 2\mid(x+1)
\land 3\mid(x-a)
\bigr).
$$

## 4. Массивы: одно равенство

$$
A=B
\land A[i]=0
\land B[i+1]=1
\land B[j]=2.
$$

## 5. Массивы: несколько равенств и совпадения индексов

$$
\begin{aligned}
&A=B\land B=C\\
&\land A[i]=0\land C[j]=1\\
&\land B[k]=A[j]\land C[i+1]=B[i].
\end{aligned}
$$

## 6. Массивы: равенства и неравенства

$$
\begin{aligned}
&A=B\land C=D\\
&\land A\ne C\land B\ne D\\
&\land A[i]=0\land C[i]=0\\
&\land B[j]=1\land D[j]=1.
\end{aligned}
$$
