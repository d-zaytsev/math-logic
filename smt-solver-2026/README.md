## smt-solver

Каждое задание — в своём файле, там, где кидается `raise NotImplementedError()`. Тесты к заданию — в том же файле.

| | Файл | Задание | Баллы |
|---|---|---|---|
| 1 | `congruence.py` | `CongruenceSolver.check` — конгруэнтное замыкание для QF_UF | 6 |
| 2 | `dpll_t.py` | `DPLL_T_Solver.check` — ленивый оффлайн-алгоритм DPLL(T) | 4 |
| 3 | `arrays.py` | `array_to_euf` — сведение формул с массивами к EUF | 5 |

Задания независимы, начинать можно с любого.

### Запуск

```
pip install -r requirements.txt
python congruence.py   # тесты одного задания
python main.py         # все тесты и баллы
```

Баллы выводятся в строке `Total points for this homework:`.
