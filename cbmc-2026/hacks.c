#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>

bool have_different_signs(int x, int y)
{
    return x >= 0 && y < 0 || x < 0 && y >= 0;
}

bool have_different_signs_optimized(int x, int y)
{
    // TODO: нельзя использовать: &&, ||, ?: (тернарный оператор условия), for, if
    return ((x ^ y) < 0);
}

void check1(int x, int y)
{
    assert(have_different_signs(x, y) == have_different_signs_optimized(x, y));
}

int abs(int x)
{
    return x > 0 ? x : -x;
}

int abs_optimized(int x)
{
    // TODO: нельзя использовать: ?: (тернарный оператор условия), for, if
    unsigned int r;
    int const mask = x >> sizeof(int) * CHAR_BIT - 1;
    r = (x + mask) ^ mask;
    return r;
}

void check2(int c)
{
    __CPROVER_assume(c > INT_MIN);
    assert(abs(c) == abs_optimized(c));
}

bool is_power_of_two(unsigned int x)
{
    int i = sizeof(unsigned int) * CHAR_BIT;
    if (!x)
        return false;
    for (; i >= 0 && x; i--)
    {
        if (x == 1)
            return true;
        if (x % 2 == 1)
            return false;
        x /= 2;
    }
}

bool is_power_of_two_optimized(unsigned int v)
{
    // TODO: нельзя использовать: ?: (тернарный оператор условия), for, if
    return v && !(v & (v - 1));
}

void check3(int c)
{
    assert(is_power_of_two(c) == is_power_of_two_optimized(c));
}
