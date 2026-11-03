// Задача 3: UpWhileNotEqual. 2 балла.
// Напишите индуктивный инвариант цикла и необходимый decreases
method UpWhileNotEqual(N: int) returns (i: int)
  requires 0 <= N
  ensures i == N
{
  i := 0;
  while i != N
    invariant 0 <= i <= N
    decreases N - i
  {
    i := i + 1;
  }
}
