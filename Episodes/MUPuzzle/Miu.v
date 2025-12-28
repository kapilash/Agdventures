
Print LoadPath.

From Stdlib Require Export String.
From Stdlib Require Export List.
From Stdlib Require Export Bool.
From Stdlib Require Export Nat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

(*From mathcomp Require Import all_ssreflect.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Not3Multiple : nat -> Prop :=
  | Remainder1 (n: nat) (H: exists k, n = 3 * k + 1) : Not3Multiple n
  | Remainder2 (n: nat) (H: exists k, n = 3 * k + 2) : Not3Multiple n.


Theorem n_not_3_multiple__2n_not_3_multiple :
  forall n: nat, Not3Multiple n -> Not3Multiple (2 * n ).
Proof.
  intros n Hnot3.
  inversion Hnot3.
  - apply Remainder2.
    destruct H as [k Hk].
    exists (2 * k).
    lia.
  - apply Remainder1.
    destruct H as [k Hk].
    exists (2 * k + 1).
    lia.
Qed.



Theorem not_3_multiple_1 : Not3Multiple 1.
Proof.
  apply Remainder1.
  exists 0.
  lia.
Qed.

Inductive miu : Type :=
  | M : miu
  | I : miu
  | U : miu.

Inductive miustr : Type :=
  | Nil : miustr
  | Cons : miu -> miustr -> miustr.

Fixpoint append (s1 s2: miustr) : miustr :=
  match s1 with
  | Nil => s2
  | Cons x xs => Cons x (append xs s2)
  end.

Fixpoint count_I (s: miustr) : nat  :=
  match s with
  | Nil => 0
  | Cons I xs => 1 + count_I xs
  | Cons _ xs => count_I xs
  end.

Fixpoint miustrlen (s: miustr) : nat :=
  match s with
  | Nil => 0
  | Cons _ xs => 1 + miustrlen xs
  end.

Inductive MiuSystem : miustr -> Prop :=
  | MIU_Axiom : MiuSystem (Cons M (Cons I Nil))
  | MIU_Rule1 : forall s, MiuSystem (append s (Cons I Nil))  -> MiuSystem (append  s (Cons I (Cons U Nil)))
  | MIU_Rule2 : forall s, MiuSystem (Cons M s) -> MiuSystem (Cons M (append s s))
  | MIU_Rule3 : forall s1 s2, MiuSystem (append s1 (Cons I (Cons I (Cons I s2)))) -> MiuSystem (append s1 (Cons U s2))
  | MIU_Rule4 : forall s1 s2, MiuSystem (append s1 (Cons U (Cons U s2))) -> MiuSystem (append s1 s2).


Theorem countI_axiom_not_3_multiple :
  Not3Multiple (count_I (Cons M (Cons I Nil))).
Proof.
  simpl.
  apply not_3_multiple_1.
Qed.


Theorem assoc_countI_append :
  forall s1 s2: miustr,
    count_I (append s1 s2) = count_I s1 + count_I s2.
Proof.
  intros s1 s2.
  induction s1 as [| x xs IH].
  - simpl. reflexivity.
  - simpl.
    induction x.
    + simpl. rewrite IH. lia.
    + simpl. rewrite IH. lia.
    + simpl. rewrite IH. lia.
Qed.

Theorem rule1_preserves_not_3_multiple :
  forall s: miustr,
    Not3Multiple (count_I (append s (Cons I Nil))) ->
    Not3Multiple (count_I (append s (Cons I (Cons U Nil)))).
Proof.
  intros s Hnot3.
  rewrite assoc_countI_append.
  rewrite assoc_countI_append in Hnot3.
  assert (G : count_I (Cons I (Cons U Nil)) = 1).
  { simpl. reflexivity. }
  rewrite G.
  assert (H: count_I (Cons I Nil)  = 1 ). 
  { simpl. reflexivity. }
  rewrite H in Hnot3.
  assumption.
Qed.

Theorem rule2_preserves_not_3_multiple :
  forall s: miustr,
    Not3Multiple (count_I (Cons M s)) ->
    Not3Multiple (count_I (Cons M (append s s))).
Proof.
  intros s  Hnot3.
  simpl.
  rewrite assoc_countI_append.
  assert(G : count_I (Cons M s) = count_I s).
  { simpl. reflexivity. }
  rewrite G in Hnot3.
  assert (Hdouble : count_I s + count_I s = 2 * count_I s).
  { lia. }
  rewrite Hdouble.
  apply n_not_3_multiple__2n_not_3_multiple.
  assumption.
Qed.

Theorem rule4_preserves_not_3_multiple :
  forall s1 s2: miustr,
    Not3Multiple (count_I (append s1 (Cons U (Cons U s2)))) ->
    Not3Multiple (count_I (append s1 s2)).
Proof.
  intros s1 s2 Hnot3.
  simpl.
  rewrite assoc_countI_append.
  assert (G1: count_I (Cons U (Cons U s2)) = count_I s2).
  { simpl. reflexivity. }
  rewrite assoc_countI_append in Hnot3.
  rewrite G1 in Hnot3.
  assumption.
Qed.

Theorem count_I_reduces_by_3_rule3 :
  forall s1 s2: miustr, 
    count_I (append s1 (Cons I (Cons I (Cons I s2)))) = count_I (append s1 (Cons U s2)) + 3.
Proof.
  intros s1 s2.
  simpl.
  rewrite assoc_countI_append.
  rewrite assoc_countI_append.
  simpl.
  lia.
Qed.

Theorem np3nm__n_nm:
  forall n: nat, Not3Multiple (n + 3) ->  Not3Multiple n.
Proof.
  intros n Hnot3.
  inversion Hnot3.
  - apply Remainder1.
    destruct H as [k Hk].
    exists (k - 1).
    lia.
  - apply Remainder2.
    destruct H as [k Hk].
    exists (k - 1).
    lia.
Qed.
                    
Theorem rule3_preserves_not_3_multiple :
  forall s1 s2: miustr,
    Not3Multiple (count_I (append s1 (Cons I (Cons I (Cons I s2))))) ->
    Not3Multiple (count_I (append s1 (Cons U s2))).
Proof.
  intros s1 s2 Hnot3.
  
  assert (G1 : count_I (append s1 (Cons U s2)) = count_I s1 + (count_I s2)).
  { simpl.
    rewrite assoc_countI_append.
    simpl.
    reflexivity.
  }
  rewrite G1.
  rewrite count_I_reduces_by_3_rule3 in Hnot3.
  rewrite G1 in Hnot3.
  apply np3nm__n_nm in Hnot3.
  assumption.
Qed.

Theorem miuderivable_countI_not_3_multiple :
   forall s : miustr,
    MiuSystem s -> Not3Multiple (count_I s).
Proof.
  intros s Hmid.
  induction Hmid.
  - apply countI_axiom_not_3_multiple.
  - apply rule1_preserves_not_3_multiple.
    assumption.
  - apply rule2_preserves_not_3_multiple.
    assumption.
  - apply rule3_preserves_not_3_multiple.
    assumption.
  - apply rule4_preserves_not_3_multiple.
    assumption.
Qed.

Theorem mu_not_derivable :
  ~ MiuSystem (Cons M (Cons U Nil)).
Proof.
  intros Hderiv.
  apply miuderivable_countI_not_3_multiple in Hderiv.
  simpl in Hderiv.
  inversion Hderiv.
  - destruct H as [k Hk].
    simpl in Hk.
    lia.
  - destruct H as [k Hk].
    simpl in Hk.
    lia.
Qed.



