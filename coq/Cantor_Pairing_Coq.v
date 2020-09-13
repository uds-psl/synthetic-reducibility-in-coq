(* Cantor's Pairing Function of natural numbers, code by Andrej Dudenhefner *)

From Coq Require Import PeanoNat.
Import Nat.

Section Cantor.

Implicit Types (n x y: nat) (c: nat * nat).

Definition next c : nat * nat :=
  match c with
  | (0,y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

Fixpoint nat_to_nat2 n : nat * nat :=
  match n with
  | 0 => (0,0)
  | S n' => next (nat_to_nat2 n')
  end.

Fixpoint sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + sum n'
  end.

Definition nat2_to_nat '(x, y) : nat :=
  sum (x + y) + y.

Fact nat2_to_nat_next c :
  nat2_to_nat (next c) = S (nat2_to_nat c).
Proof.
  destruct c as [[|x] y]; cbn -[sum].
  - rewrite !add_0_r. rewrite add_comm. reflexivity.
  - rewrite !add_succ_r. reflexivity.
Qed.

Fact nat2_to_nat_nat_to_nat2_cancel n :
  nat2_to_nat (nat_to_nat2 n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite nat2_to_nat_next, IH. reflexivity.
Qed.

Fact nat_to_nat2_nat2_to_nat_cancel c :
  nat_to_nat2 (nat2_to_nat c) = c.
Proof.
  revert c.
  enough (forall n c, nat2_to_nat c = n -> nat_to_nat2 n = c) by eauto.
  induction n as [|n IH]; intros [x y]; cbn [nat_to_nat2].
  - destruct x, y.
    1:reflexivity. all:intros [=].
  - destruct y. 1:destruct x.
    + intros [=].
    + change (S x, 0) with (next (0,x)).
      rewrite nat2_to_nat_next. intros H. f_equal.
      apply IH. congruence.
     + change (x, S y) with (next (S x, y)). 
      rewrite nat2_to_nat_next. intros H. f_equal.
      apply IH. congruence.
Qed.
End Cantor.

(* End of the code from Andrej Dudenhefner *) 
