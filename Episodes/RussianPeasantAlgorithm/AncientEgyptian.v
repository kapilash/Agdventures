From Stdlib Require Export String.
From Stdlib Require Export List.
From Stdlib Require Export Bool.
From Stdlib Require Export Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Print nat.


Inductive Even : nat -> Prop :=
  | Even0 : Even 0
  | EvenSS (n: nat) (H: Even n) : Even (S (S n)).


Inductive Odd : nat -> Prop :=
  | Odd1 : Odd 1
  | OddSS (n: nat) (H: Odd n) : Odd (S (S n)).


Fixpoint half (n: nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (half n')
  end.

Fixpoint double (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.


Inductive EgyptianMultiplication : nat -> nat -> nat -> Prop :=
  | EM_Zero (n: nat) : EgyptianMultiplication 0 n 0
  | EM_One (n: nat) : EgyptianMultiplication 1 n n
  | EM_Even (m n r: nat) (H0: Even m) (H2: EgyptianMultiplication (half m) (double n) r) : EgyptianMultiplication m n r
  | EM_Odd (m n r1 r2: nat) (H0 : Odd m) (H1: EgyptianMultiplication (half m) (double n) r1) (H2: r2 = r1 + n) : EgyptianMultiplication m n r2.



Lemma double_x2 : forall n: nat, double  n = 2 * n.
Proof.
  intros n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. lia.
Qed.
    
Lemma half_ssn_eq_half_n_plus_1 : forall n: nat, half (S (S n)) = S (half n).
Proof.
  intros n.
  simpl. reflexivity.
Qed.


Lemma even_x__half_x_double_y_eq_xy :
  forall x y: nat, Even x -> (half x) * (double y) =  x * y.
Proof.
  intros x y H. induction H as [| n' H' IH].
  - simpl. reflexivity.
  - rewrite half_ssn_eq_half_n_plus_1.
    rewrite Nat.mul_succ_l with (n := half n') (m := double y).
    rewrite double_x2 in *.
    lia.
Qed.

Lemma odd_x__half_x_double_y_plus_y_eq_xy_plus_y :
  forall x y: nat, Odd x -> (half x) * (double y) + y = x * y.
Proof.
  intros x y H. induction H as [| n' H' IH].
  - simpl. lia.
  - rewrite half_ssn_eq_half_n_plus_1.
    rewrite Nat.mul_succ_l with (n := half n') (m := double y).
    rewrite double_x2 in *.
    lia.
Qed.


Theorem egyptian_multiplication_correct :
  forall m n r: nat, EgyptianMultiplication m n r -> r = m * n.
Proof.
  intros m n r H. induction H as [n' | n' | m' n' r' H0 IH | m' n' r1 r2 H0 IH1 H2].
  - simpl. reflexivity.
  - simpl. lia.
  - assert (G: half m' * double n' = m' * n').
    { apply  even_x__half_x_double_y_eq_xy with (x := m') (y := n'). apply H0.}
    rewrite <- G.
    assumption.
  - assert (G: half m' * double n' + n' = m' * n').
    { apply odd_x__half_x_double_y_plus_y_eq_xy_plus_y with (x := m') (y := n').
      apply H0.}
   rewrite <- G.
    rewrite H2 in H1.
    assumption.
Qed.
