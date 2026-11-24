#include <stdint.h>
#include <stdio.h>
#include <assert.h>
#include <limits.h>
#include <stdbool.h>

void sort(int *a, size_t n)
{
    for (size_t i = 0; i < n; i++)
    {
        for (size_t j = i + 1; j < n; j++)
        {
            if (a[i] > a[j])
            {
                int tmp = a[i];
                a[i] = a[j];
                a[j] = tmp;
            }
        }
    }
}

extern int nondet_int(void);

void check()
{
    int a[LEN];

    for (int i = 0; i < LEN; i++)
        a[i] = nondet_int();

    sort(a, LEN);

    for (int i = 1; i < LEN; i++)
    {
        assert(a[i] >= a[i - 1]);
    }
    // TODO: здесь нужно написать свои ограничения, которые гарантируют следующее:
    // TODO: массив `a` действительно отсортирован по возрастанию
    // TODO: подсказка: напишите вспомогательную функцию
}
