# coq-natural-deduction

Работоспособность проверялась на Coq 8.20

Порядок решения задач:

- заменить `Admitted` на доказательства в файле [NaturalDeduction.v](NaturalDeduction.v);

## Баллы

- Каждая задача в `NaturalDeduction.v` стоит 2 балла
- Всего можно набрать 10 баллов

## При решении задач в файле `NaturalDeduction.v`

**Можно**:

- пользоваться тактиками: `intros, intro, elim, apply, exact, split, left, right, assumption, unfold, specialize, assert`;
- пользоваться [intro-паттернами](https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns), например `intros [[Hx Hy] | [Ha Hb]]`;

**Запрещено**:

- переиспользовать уже существующие леммы;
- писать свои тактики;
- пользоваться автоматизирующими тактиками, такими как: `auto`, `trivial`, `easy`, `intuition`, `firstorder` и т.п. Если в задаче использована такая тактика, **вся задача не засчитывается**.
