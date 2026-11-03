// Задача 11: Fib. 4 балла.
// Напишите метод, реализующий вычисление n-ного числа Фибоначчи за линейное время
function fib(n: nat): nat
{
  if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)
}

method Fib(n: nat) returns (result: nat)
  ensures result == fib(n)
{
  if n == 0 || n == 1 { return 1; }

  var i := 1;
  result := 1;
  var prev := 1;

  while i < n
    invariant 1 <= i <= n
    invariant result == fib(i)
    invariant prev == fib(i - 1)
  {
    result, prev := result + prev, result;
    i := i + 1;
  }
}
