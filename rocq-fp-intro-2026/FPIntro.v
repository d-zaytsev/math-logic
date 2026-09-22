Inductive bool : Type :=
  | true
  | false.

(* Check позволяет проверить тип *)
Check false.

(* Definition позволяет давать имена выражениям, например, определять функции *)
Definition negb (b:bool) : bool :=
  match b with (* сопоставление с образцом *)
  | true => false
  | false => true
  end.

(* Compute позволяет вычислять *)
Compute (negb (negb (negb false))).
Check negb.
(* Print выведет определение *)
Print negb.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Notation позволяет определять свои нотации *)
Notation "x && y" := (andb x y).
Compute (false && true && true).

(* Inductive позволяет определять индуктивные типы (обобщение АТД из Хаскеля) *)
Inductive nat : Type :=
  | O
  | S (x : nat).

Definition one := S O.
Definition two := S one.

(* Для лямбда функций есть свой синтаксис *)
Definition plus2 : nat -> nat := fun x => S (S x).
Check plus2.
Compute (plus2 two).

(* Definition не допускает рекурсии. Fixpoint позволяет определять завершающиеся рекурсивные функции. *)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Compute (even (plus2 one)).
Compute (even (plus2 two)).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y).

Compute (two + two).

(* Exercise: напишите функцию умножения двух чисел *)
Fixpoint mult (n : nat) (m : nat) : nat := 
    match n with
    | O => O
    | S O => m
    | S n' => mult n' (plus m m) 
    end.
Notation "x * y" := (mult x y).

Compute (two * (S two)).
(* Exercise: напишите функцию факториала *)
Fixpoint fac (n : nat) : nat := 
    match n with
    | O => one
    | S O => one
    | S n' => plus n (fac n') 
    end.

Compute (fac (S (S (S O)))).
(* Exercise: напишите функцию возведения в степень *)
Fixpoint pow (n : nat) (m : nat) : nat := 
    match m with
    | O => one
    | S O => n
    | S m' => pow (mult n n) m'
    end.

Notation "x ^ y" := (pow x y).
Compute (two ^ two).


(* Можно сопоставлять с образцом сразу несколько переменных *)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.
Notation "x == y" := (eqb x y) (at level 55).

Compute (two + two == plus2 two).

(* Первая теорема. Объявляются командами Theorem, Lemma, Example и т.д. (всё синонимы). *)
Theorem plus_O_n : forall n : nat, n = O + n.
Proof.
  intros n. (* "пусть есть число n" *)
  simpl. (* O + n можно частично вычислить, раскрыв определение "+" *)
  reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Example mult_0_l : forall n:nat, O = O * n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H. (* допустим, n = m (назовём гипотезу H) *)
  rewrite -> H. (* раз знаем, что n = m, можно всюду n заменить на m *)
  reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2. (* допустим, n = m (назовём гипотезу H) *)
  rewrite -> H1. (* раз знаем, что n = m, можно всюду n заменить на m *)
  rewrite -> H2. (* раз знаем, что n = m, можно всюду n заменить на m *)
  reflexivity.
Qed.

Theorem plus_n_0_m_0 : forall p q : nat,
  (O + p) + (O + q) = p + q.
Proof.
  intros p q. (* что-то похожее уже доказывали, как переиспользовать? *)
  Check plus_O_n.
  rewrite <- plus_O_n. (* переписываем при помощи известной теоремы *)
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat, (n + one == O) = false.
Proof.
  intros n. 
  simpl. (* 1 справа, ничего не упрощается *)
  destruct n as [| n'] eqn:E. (* тактика для разбора случаев *)
  - unfold "+". (* unfold раскрывает и упрощает *)
    reflexivity.
  - unfold "+". fold plus. (* fold сворачивает определение *)
    unfold "==". reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros n.
  simpl.
  destruct n as [| n'] eqn:E.
  - unfold negb.
    reflexivity.
  - unfold negb.
    reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  - unfold andb in H. exact H.
  - unfold andb in H. discriminate H. 
Qed.

Theorem add_0_r : forall n:nat,
  n + O = n.
Proof.
  (* intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* свели задачу к себе самой... нужна индукция! *)
  Undo 5. *)
  induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
  n * O = O.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. destruct n'; reflexivity.
Qed.

(* Exercise *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - unfold "+". reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

(* Exercise *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

(* Exercise *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
    intros n m p.
    induction n as [| n' IHn'].
    - simpl. rewrite add_comm. reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* Exercise: напишите функцию, которая возвращает список из count элементов, каждый из которых n *)
Fixpoint repeat (n count : nat) : natlist := [].

(* Exercise *)
Theorem length_of_repeat : forall (n count : nat), length (repeat n count) = count.
Proof. Admitted.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y).

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| x l1 IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ h :: []
  end.

(* Используется дальше *)
Lemma app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - simpl. rewrite <- IHl'.
    (* stuck *)
    rewrite -> app_length.
    simpl.
    rewrite add_comm. reflexivity.
Qed.

Fixpoint map (f : nat -> nat) (xs : natlist) : natlist :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'
  end.

Theorem map_compose : forall f g xs, map f (map g xs) = map (fun x => f (g x)) xs.
Proof.
  intros f g xs. induction xs as [| x xs IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

(* Exercise: напишите функцию фильтрации по предикату *)
Fixpoint filter (p : nat -> bool) (xs : natlist) : natlist := [].

(* Exercise *)
Theorem filter_map : forall f p xs,
  filter p (map f xs) = map f (filter (fun x => p (f x)) xs).
Proof. Admitted.
