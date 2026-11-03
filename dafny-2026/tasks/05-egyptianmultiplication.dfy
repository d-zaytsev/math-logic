// Задача 5: EgyptianMultiplication. 3 балла.
// Напишите индуктивный инвариант цикла
method EgyptianMultiplication(x: nat, y: nat) returns (res: nat)
  ensures res == x * y
{
  var a: nat := x;
  var b: nat := y;
  res := 0;
  while a > 0
    invariant res + (a * b) == x * y 
  {
    assert a == 2 * (a / 2) + a % 2;
    if a % 2 == 1 {
      res := res + b;
    }
    a := a / 2;
    b := b * 2;
  }
  return res;
}
