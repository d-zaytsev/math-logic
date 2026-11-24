#include <stdio.h>
#include <assert.h>

unsigned search(char *s, unsigned len)
{
    if (len < 3)
        return len; // not found
    unsigned seen = 0;
    for (unsigned i = 0; i < len; i++)
    {
        char ch = s[i]; // других чтений s[...] не должно быть
        if (seen == 0 && ch == '+')
            seen = 1;
        else if (seen == 1 && ch == '+')
            seen = 2;
        else if (seen == 2 && ch == 'x')
            return i - 2; // found
        else
            seen = 0; // reset
    }
    return len; // not found
}

unsigned simple_search(char *s, unsigned len)
{
    if (len < 3)
        return len;

    for (unsigned i = 0; i < len - 2; i++)
    {
        if (s[i] == '+' && s[i + 1] == '+' && s[i + 2] == 'x')
            return i;
    }

    return len;
}

int main()
{
    char s[LEN];

    for (int i = 0; i < LEN; i++)
        s[i] = nondet_char();

    for (unsigned i = 2; i < LEN; ++i)
    {
        __CPROVER_assume(!(s[i - 2] == '+' &&
                           s[i - 1] == '+' &&
                           s[i] == '+'));
    }

    assert(simple_search(s, LEN) == search(s, LEN));
    // TODO: здесь нужно написать свои ограничения, которые гарантируют следующее:
    // TODO: функция `search(s, len)` возвращает индекс в `s` начала подстроки `++x`, если эта подстрока есть в строке `s`, иначе возвращает `len`
    // TODO: подсказка: напишите вспомогательную неоптимальную функцию для этой же задачи
    return 0;
}
