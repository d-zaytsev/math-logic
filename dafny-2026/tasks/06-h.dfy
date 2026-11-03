// Задача 6: H. 1 балл.
// Напишите необходимый decreases
function H(x: int): int
  decreases x + 60 // TODO: мера завершения
{
  if x < -60 then x else H(x - 1)
}
