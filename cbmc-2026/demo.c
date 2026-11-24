#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

//// all asserts in file
// cbmc --show-properties demo.c
//// run specific property
// cbmc --property check_abs.assertion.1 demo.c
//// no entry point: file has no main, we want to start from custom function `check_abs`
// cbmc --function check_abs --property check_abs.assertion.1 demo.c
//// CBMC tells us there is a bug! We want to see a counterexample trace
// cbmc --trace --function check_abs --property check_abs.assertion.1 demo.c
//// let's try it
// write `test` function
// gcc -nostartfiles -Wl,--entry="test" demo.c && ./a.out
//// ok, suppose we are ok with it, so let's fix our specification
// add `__CPROVER_assume` - it limits cases which will be considered
// cbmc --trace --function check_abs --property check_abs.assertion.1 demo.c
//// now VERIFICATION SUCCESSFUL!

int abs(int x)
{
    if (x >= 0)
        return x;
    else
        return -x;
}

void check_abs(int x)
{
    __CPROVER_assume(x > -2147483648);
    assert(abs(x) >= 0);
}

int test()
{
    printf("%d\n", abs(-2147483648));
    exit(0);
}

//// factorize with cbmc
// cbmc --trace --function check_notprime --property factorize.assertion.1 demo.c | grep INPUT
//// factorize prime number: "SUCCESS" means assert never fails, so no factorization
// cbmc --trace --function check_prime --property factorize.assertion.1 demo.c
//// cbmc reduces everything to SAT, so we can extract SAT encoding
// cbmc  --function check_notprime --property factorize.assertion.1 --dimacs --outfile factor.cnf demo.c
//// usual DIMACS, let's try to understand, e.g., extract variables
// code factor.cnf, find `c check_notprime::a!0@1#1` and `c check_notprime::b!0@1#1`
//// run of-the-shelf SAT solver and learn factors from it
// kissat -q factor.cnf, copy vars according to above to demo.py
// python demo.py
//// indeed the same values! so CBMC is fair: it is just a transformer from C into DIMACS

void factorize(unsigned int p, unsigned int q, unsigned long long z)
{
    unsigned long long x = p;
    unsigned long long y = q;
    assert(!(x * y == z && x > 1 && y > 1));
}

void check_notprime(unsigned int a, unsigned int b)
{
    factorize(a, b, 45600119);
}

void check_prime(unsigned int a, unsigned int b)
{
    factorize(a, b, 5437);
}

//// loops need an unwinding bound
// cbmc demo.c --function check_loop --property check_loop.assertion.1 --unwind 4 --trace
//// the bound is sufficient for n <= 3: the loop body is executed at most four times

void check_loop(unsigned n)
{
    __CPROVER_assume(n <= 3);

    unsigned i = 0;
    while (i < n)
    {
        i++;
    }

    assert(i == n);
}

//// BMC is not a silver bullet: precise memory modelling is too hard for it
// cbmc --function check_pointers --trace demo.c
//// it is successful despite we have a counterexample in mind
// code demo2.c, gcc demo2.c && ./a.out
//// more precise memory management relying on more expressive logic with equalities, arrays and stuff
//// will come later when we will speak about symbolic execution and SMT solving

void check_pointers(char *s1, char *s2)
{
    __CPROVER_assume(s1 != NULL && s2 != NULL);
    s1[0] = 42;
    s2[0] = 43;
    assert(s1[0] != s2[0]);
}
