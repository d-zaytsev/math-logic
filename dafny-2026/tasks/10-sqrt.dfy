// Задача 10: Sqrt. 3 балла.
// Напишите метод, реализующий вычисление корня из натурального числа пробегом от 0 до этого числа, пока не найдётся нужный корень
// Корень должен быть с округлением вниз, примеры указаны внизу в ensures
method Sqrt(n: nat) returns (result: nat)
  ensures n == 0 ==> result == 0
  ensures n == 1 ==> result == 1
  ensures n == 2 ==> result == 1
  ensures n == 3 ==> result == 1
  ensures n == 4 ==> result == 2
  ensures result * result <= n < (result + 1) * (result + 1)
{
  result := 0;
  while (result + 1) * (result + 1) <= n
    invariant result * result <= n
    decreases n - result
  {
    result := result + 1;
  }
}
