(* Recursive Mu-Operator and Inverse Functions *)
From Coq Require Import Arith Lia.
Require Export List.

Require Import Preliminaries_Coq Preliminaries_Lists_Coq Definitions_Coq.

(* Recursive Mu-Operator and deduced Witness Operator *)

(* Coded adapted from Gert Smolka, Lecture Notes ICL, 2019 *)

Section Mu_Operator.
  
  (* Operator for Decidable Predicates *)

  Definition least (p: nat -> Prop) k n : Prop
    := n <= k /\ p k /\ forall m, n <= m -> p m -> k <= m.

  Inductive G (p: nat -> Prop) (n: nat) : Prop :=
  | GI : (~ p n -> G p (S n)) -> G p n.

  Lemma G_sig {p: nat -> Prop} (n: nat) :
    dec_pred p -> G p n -> {k | least p k n}.
  Proof.
    intros D. induction 1 as [n _ IH].
    destruct (D n).
    - exists n. firstorder.
    - specialize (IH n0) as [k IH]. 
      exists k. firstorder. lia.
      destruct H2.
      + contradiction n0.
      + apply H1; firstorder. lia.
  Defined.

  Lemma G_zero {p: nat -> Prop} (n: nat) :
    G p n -> G p 0.
  Proof.
    induction n as [|n IH].
    - intros H. exact H.
    - intros H. apply IH. constructor. intros _. exact H.
  Qed.

  Lemma G_ex {p: nat -> Prop} :
    (exists n, p n) -> exists n, G p n.
  Proof.
    intros [n pn].
    exists n. 
    constructor. firstorder.
  Qed.
   
  Definition mu_NN_sig (p : nat -> Prop): 
    dec_pred p -> ex p -> {n | p n /\ forall m, p m -> n <= m}.
  Proof.
    intros D H.
    assert {n | least p n 0} as [n L]. 
    - apply (G_sig 0 D). destruct (G_ex H). apply (G_zero x), H0.
    - exists n; firstorder. apply H2; firstorder. lia.
  Qed.     

  Definition mu_NN (p: nat -> Prop) D H : nat
    := proj1_sig (mu_NN_sig p D H).
    
  Definition mu_NN_spec p D H 
    := proj2_sig (mu_NN_sig p D H).

  Definition wo_NN_sig (p : nat -> Prop):
    dec_pred p -> ex p -> {n | p n }.
  Proof.
    intros H E.
    destruct (mu_NN_sig p H E) as [n [H1 _]].
    exists n. exact H1.
  Qed.

  Definition wo_T_sig {X} (f: nat -> X) (p: X -> Prop): 
    surjective f -> dec_pred p -> ex p -> sig p.
  Proof.
    intros S D Ex. remember (wo_NN_sig (fun n => p (f n))).
    destruct s; firstorder. destruct (S x). exists x0. now rewrite H0.
  Qed. 

  Lemma constant_mu (p : nat -> Prop):
    forall D H1 H2, mu_NN p D H1 = mu_NN p D H2.
  Proof.
    intros D H1 H2. 
    set (W1:= mu_NN_spec p D H1). 
    set (W2:= mu_NN_spec p D H2).
    destruct W1 as [p1 L1], W2 as [p2 L2].
    specialize (L2 (mu_NN p D H1)).
    specialize (L1 (mu_NN p D H2)).
    apply L2 in p1. apply L1 in p2. unfold mu_NN in *. lia.
  Qed. 


  (* Mu-Operator and deduced Witness Operator for Enumerable Predicates *)
   
  Lemma proof_computation {X} (p : X -> Prop) f:
    enumerator p f -> (exists y, p y) 
      -> exists n y, f n = Some y.
  Proof.
    intros E [y [n py] % E].
    eauto. 
  Qed.

  Definition mu_enum_NN_sig {X} (p : X -> Prop) f:
    enumerator p f -> ex p -> 
      {n | (exists x, f n = Some x) /\ 
        (forall n1, (exists x1, (f n1) = Some x1) -> n <= n1) }.
  Proof.
    intros E H.
    assert (exists n x, f n = Some x) by exact (proof_computation p f E H).
    eapply mu_NN_sig in H0 as (? & ?).
    - exists x.  exact a.
    - intros n. destruct (f n). 
      + left. eauto.
      + right. intros []. inversion H1.
  Defined.

  Definition mu_enum_NN {X} (p: X -> Prop) f E H : nat
    := proj1_sig (mu_enum_NN_sig p f E H).

  Definition mu_enum_NN_spec {X} (p: X -> Prop) f E H 
    := proj2_sig (mu_enum_NN_sig p f E H).

  Definition mu_enum_sig {X} (p : X -> Prop) f :
    forall E H, {x | p x /\ Some x = f (mu_enum_NN p f E H)}.
  Proof.
    intros E H.
    - destruct (f (mu_enum_NN p f E H)) eqn: H2.
      + exists x. 
        intuition. apply E. eauto.
      + exfalso. remember (mu_enum_NN_spec p f E H). destruct a as [[x a1] a2].
        unfold mu_enum_NN in H2. rewrite a1 in H2. discriminate.
  Defined.

  Definition mu_enum {X} (p: X -> Prop) f E H : X
    := proj1_sig (mu_enum_sig p f E H).

  Definition mu_enum_spec {X} (p: X -> Prop) f E H 
    := proj2_sig (mu_enum_sig p f E H).

  Definition wo_enum_sig {X} (p : X -> Prop) f:
    enumerator p f -> (exists x, p x) -> {x | p x}.
  Proof.
    intros E H. destruct (mu_enum_sig p f E H).
    exists x. intuition.
  Defined.

  Lemma constant_mu_enum_NN {X} (p : X -> Prop) f E:
    forall H1 H2, mu_enum_NN p f E H1 = mu_enum_NN p f E H2.
  Proof.
    intros H1 H2.
    set (W1:= mu_enum_NN_spec p f E H1). 
    set (W2:= mu_enum_NN_spec p f E H2).
    destruct W1 as [p1 L1], W2 as [p2 L2].
    specialize (L2 (mu_enum_NN p f E H1)).
    specialize (L1 (mu_enum_NN p f E H2)).
    apply L2 in p1. apply L1 in p2. 
    unfold mu_enum_NN in *. lia.
  Qed.

  Lemma mu_enum_agree {X} (p : X -> Prop) f E H:
    f (mu_enum_NN p f E H) = Some (mu_enum p f E H).
  Proof.
    remember (mu_enum_spec p f E H). cbn in a. destruct a as [a1 a2].
    unfold mu_enum. rewrite a2. trivial.
  Qed.

  Lemma constant_mu_enum {X} (p : X -> Prop) f E:
    forall H1 H2, mu_enum p f E H1 = mu_enum p f E H2.
  Proof.  
    intros H1 H2.
    assert 
      (Some (mu_enum p f E H1) = Some (mu_enum p f E H2)).
    - rewrite <- (mu_enum_agree p f E H1).
      rewrite <- (mu_enum_agree p f E H2).
      rewrite (constant_mu_enum_NN p f E H1 H2). 
      trivial.
    - inversion H. trivial. 
  Qed. 

End Mu_Operator. 

(* End of adaption from Gert Smolka *)


(* (Right-) Inverse Function for Bijections (Surjections) with Enumerable Domain and Discrete Co-Domain *)

Section Inverse_Enum_T.

  Definition inverse {X Y} (f: X -> Y) g : Prop
    := (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

  Context {X Y:Type}.

  Variable D: discrete Y.
  Variable E_X: nat -> X.
  Variable Surj_E_X: surjective E_X.

  Implicit Types (f : X -> Y) (g : Y -> X).

  Theorem wo_inverse {f}:
      forall y, (exists x, f x = y) -> {x | f x = y}.
  Proof.
    intros y H. apply (wo_T_sig E_X); intuition.    
    intros n. exact (D (f n, y)).
  Qed.

  Lemma Right_Inv_sig f: 
    surjective f -> {g | forall x, f (g x) = x}.
  Proof.
    intros E.
    assert (forall y, {x | f x = y}) as H.
    - intros y. apply wo_inverse. exact (E y).
    - exists (fun y => proj1_sig (H y)).
      intros y. destruct (H y). trivial.
  Qed.

  Definition Right_Inv f Su : Y -> X
    := proj1_sig (Right_Inv_sig f Su).

  Definition Right_Inv_spec f Su 
    := proj2_sig (Right_Inv_sig f Su).

  Lemma Right_Inv_inj f Su:
    injective (Right_Inv f Su).
  Proof.
    intros x1 x2 H. 
    remember (Right_Inv_spec f Su). cbn in e. unfold Right_Inv in H. 
    now rewrite <- (e x1), <- (e x2), H.
  Qed. 

  Lemma inv_sig f:
    bijective f -> {g & inverse f g}.
  Proof.
    intros [In Su].
    assert (forall x, {n | f n = x}) as H.
    - intros x. apply wo_inverse. exact (Su x).
    - exists (fun y => proj1_sig (H y)).
      split.
      + intros x. destruct (H (f x)). apply In , e.
      + intros y. destruct (H y), e. trivial.
  Qed. 

  Definition inv f (bijf: bijective f) : Y -> X
    := projT1 (inv_sig f bijf).

  Definition inv_spec f bijf
    := projT2 (inv_sig f bijf).

  Lemma inv_bij f (bijf: bijective f) :
    bijective (inv f bijf).
  Proof.
    split.
    - intros x1 x2 E. unfold inv in E. 
      now rewrite <- (proj2 (inv_spec f bijf) x1),  <- (proj2 (inv_spec f bijf) x2), E.
    - intros n.     
      exists (f n). exact (proj1 (inv_spec f bijf) n). 
  Qed.

End Inverse_Enum_T.


(* Inverse Function on Nat *)

Section Inverse_Nat.

  Context {Y:Type}.

  Variable D: discrete Y.

  Definition E_N := fun (n: nat) => n.

  Lemma Surj_E_N: surjective E_N.
  Proof.
    intros n; now exists n.
  Qed.

  Definition Right_Inv_N f Su : Y -> nat
    := proj1_sig (Right_Inv_sig D E_N Surj_E_N f Su).

  Definition Right_Inv_spec_N f Su 
    := proj2_sig (Right_Inv_sig D E_N Surj_E_N f Su).

  Lemma Right_Inv_inj_N f Su:
    injective (Right_Inv_N f Su).
  Proof.
    apply Right_Inv_inj. 
  Qed. 

  Definition inv_N f (bijf: bijective f) : Y -> nat 
    := projT1 (inv_sig D E_N Surj_E_N f bijf).

  Definition inv_spec_N f bijf
    := projT2 (inv_sig D E_N Surj_E_N f bijf).

  Lemma inv_bij_N f (bijf: bijective f) :
    bijective (inv_N f bijf).
  Proof.
    apply inv_bij.
  Qed.

End Inverse_Nat. 


(* Corollaries *)

Corollary fstL_in_sig {X Y} (f: nat -> Y) (DXY: discrete (prod X Y)) (x: X) (L: list (X * Y)):
  surjective f -> In x (fstL L) -> {y | In (x,y) L}.
Proof.
  intros S H. eapply wo_T_sig.
  - exact S. 
  - intros y. destruct (dec_membership DXY L (x,y)); firstorder.
  - apply fstL_in, H.
Qed.

Corollary datatype_iso_inv {X Y}:
  enumerable_T X -> discrete Y-> type_iso X Y -> type_iso Y X.
Proof.
  intros [f H] DY [I H1].
  exists (inv DY f H I H1).
  exact (inv_bij DY f H I H1).
Qed.

