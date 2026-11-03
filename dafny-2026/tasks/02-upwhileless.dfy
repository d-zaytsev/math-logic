// Задача 2: UpWhileLess. 1 балл.
// Напишите индуктивный инвариант цикла
method UpWhileLess(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i < N
    invariant 0 <= i <= N
  {
    i := i + 1;
  }
}
