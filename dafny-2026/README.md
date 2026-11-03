# Dafny

## Окружение и проверка

Используйте **Dafny 4.11.0**: [официальная сборка](https://github.com/dafny-lang/dafny/releases/tag/v4.11.0). Можно работать в VS Code с расширением Dafny или запускать проверку из терминала.

```sh
dafny --version
# Проверка отдельной задачи:
dafny verify tasks/01-max.dfy
# Проверка всех задач, подключённых в main.dfy:
dafny verify --verify-included-files main.dfy
```

Если используете DLL напрямую, замените `dafny` на `dotnet /path/to/Dafny.dll`.

## Задания и оценивание

В наборе 12 независимых задач, максимум 30 баллов.

| № | Задача | Баллы |
|---|---|---:|
| 1 | Max | 1 |
| 2 | UpWhileLess | 1 |
| 3 | UpWhileNotEqual | 2 |
| 4 | Sqrt2 | 3 |
| 5 | EgyptianMultiplication | 3 |
| 6 | H | 1 |
| 7 | L | 1 |
| 8 | M | 2 |
| 9 | SumTo | 3 |
| 10 | Sqrt | 3 |
| 11 | Fib | 4 |
| 12 | DivModFast | 6 |
| | **Всего** | **30** |
