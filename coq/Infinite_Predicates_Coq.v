(* Infinite Predicates *)

Require Export List.
Import ListNotations.

From Coq Require Import Arith Lia.

Require Import Preliminaries_Coq Preliminaries_Lists_Coq 
               Recursive_Mu_Operator_Coq Definitions_Coq Synthetic_Computability_Theory_Coq.

(* Different Notions of Infinte Predicates *)

(* Functional Notions: Surjections and Injections *)

Definition nat_surjection {X} (p: X -> Prop): Prop
  := (exists (f: X -> nat), set_surjection p (Top nat) f). 

Definition nat_injection {X} (p: X -> Prop): Prop
  := (exists (f: nat -> X), set_injection (Top nat) p f). 

(* Enumerable predicates that can be mapped surjectively to N can be mapped injectively from N *)

Section inf_surjection_to_injection.

  Context {X: Type}.
  Context {p: X -> Prop}.

  Variable E_p: nat -> option X.
  Variable Enum_E_p: enumerator p E_p.

  Variable f: X -> nat.

  Theorem wo_inj_surj:
      forall n, (exists x, p x /\ f x = n ) -> {x | p x /\ f x = n}.
  Proof.
    intros n.
    pose (E_p' := fun n0 => match E_p n0 with None => None | Some x => if D_nat (f x, n) then Some x else None end).
    apply (wo_enum_sig (fun x => p x /\ f x = n ) E_p').
    intros x. split; unfold E_p'.
    - intros [[n0 H2] % Enum_E_p H1]. exists n0. 
       rewrite H2, H1. destruct D_nat; intuition.
    - intros [n0 H1]. destruct E_p eqn: E; try discriminate.
      destruct D_nat; try discriminate.
      inversion H1. repeat rewrite <- H0; intuition.
      apply Enum_E_p; firstorder.
  Qed.

  Lemma Right_Inv_sig_p:
    set_surjection p (Top nat) f -> {g | forall n, p (g n) /\ f (g n) = n}.
  Proof.
    intros S.
    assert (forall n, {x | p x /\ f x = n}) as H.
    - intros n. apply wo_inj_surj. apply S; firstorder.
    - exists (fun n => proj1_sig (H n)).
      intros n. now destruct (H n).
  Qed.

  Definition Right_Inv_p Su : nat -> X
    := proj1_sig (Right_Inv_sig_p Su).

  Definition Right_Inv_spec_p Su 
    := proj2_sig (Right_Inv_sig_p Su).

End inf_surjection_to_injection.

Lemma inf_surjection_to_injection {X} (p: X -> Prop):
  enumerable p -> nat_surjection p -> nat_injection p.
Proof.
  intros [E_p H] [f Sur_f].
  exists (Right_Inv_p E_p H f Sur_f).  
  remember (Right_Inv_spec_p E_p H f Sur_f). cbn in a. 
  intros n1 n2 _ _ H1.  split.
  - unfold Right_Inv_p in H1. now rewrite <- (proj2 (a n1)), <- (proj2 (a n2)), H1.
  - apply a.
Qed.


(* Predicates containing Elements of any Number *)

Definition of_any_number {X} (p: X -> Prop) : Prop
  := forall n, exists L, length L = n /\ NoDup L /\ forall x, In x L -> p x.

Lemma inf_surjection_any_number {X} (p: X -> Prop):
  nat_surjection p -> of_any_number p. 
Proof.
  intros [f Surj] n. induction n.
  - exists nil; firstorder. constructor.
  - destruct IHn as (L & IH1 & IH2 & IH3).
    specialize (Surj (Preliminaries_Lists_Coq.list_max (map f L) + 1)).
    destruct Surj; firstorder. 
    exists (x::L). cbn; firstorder.
    + constructor; try assumption. 
      intros H1. eapply (list_max_not_in (map f L) (f x)).
      * lia.
      * apply in_map_iff. exists x; intuition.
    + now rewrite <- H1.
Qed.

Lemma inf_injection_any_number {X} (p: X -> Prop):
  discrete X -> nat_injection p -> of_any_number p. 
Proof.
  intros DX [f Inj] n. exists (map f (seq n n)).
  split.
  - now rewrite map_length, seq_length. 
  - split. 
    + apply (map_setinj_NoDup f (Top nat) p).
      * exact Inj.
      * firstorder.
      * exact (seq_NoDup n n).
    + intros x [x0 [E _]] % in_map_iff . 
      rewrite <- E.
      apply (Inj x0 x0 I I). trivial.   
Qed.

(* Characterizations of predicates containing elements of any number *)

Lemma of_any_number_iff1_help {X} (p: X -> Prop) n:
  (exists L, length L = n /\ NoDup L /\ forall x, In x L -> p x)  
    <-> (exists L, n <= length L /\ NoDup L /\ forall x, In x L -> p x).
Proof.
  split.
  - intros [L H]. 
    exists L. firstorder; lia. 
  - intros [L H].
    exists (firstn n L). repeat split.
    + apply firstn_length_le, H.
    + apply firstn_NoDup, H.
    + intros x H1 % firstn_elements. apply H, H1.
Qed.

Lemma of_any_number_iff1 {X} (p: X -> Prop):
  of_any_number p   
    <-> (forall n, exists L, n <= length L /\ NoDup L /\ forall x, In x L -> p x).
Proof.
  split; intros H n.
  - rewrite <- of_any_number_iff1_help. apply H.
  - rewrite of_any_number_iff1_help. apply H.
Qed.

Lemma of_any_number_iff2 {X} (p: X -> Prop):
  discrete X -> of_any_number p <-> forall L, exists x, p x /\ ~ In x L.
Proof.
  intros DX.  split.
  - intros H L.
    destruct (H (length L + 1)) as [L0 H1]. 
    assert (exists x, In x L0 /\ ~ In x L) as [x H2].
    + apply pigeonhole_exists; intuition. lia.
    + exists x; intuition.
  - intros H n. induction n.
    + exists nil; firstorder. constructor.
    + destruct IHn as [L0 IH].
      destruct (H L0).
      exists (x::L0). cbn; intuition.
      * now constructor.
      * now rewrite <- H6.
Qed. 

Lemma of_any_number_iff3 (p: nat -> Prop):
  of_any_number p <-> forall n, exists x, x >= n /\ p x. 
Proof.
  rewrite of_any_number_iff2.
  split.
  - intros H n. specialize (H (seq 0 n)) as [x [H1 H2]].
    exists x. rewrite in_seq in H2. intuition. lia. 
  - intros H L. specialize (H (Preliminaries_Lists_Coq.list_max L + 1)) as [x [H1 H2]].
    exists x. intuition. apply list_max_in in H. lia.
  - exact D_nat.
Qed.

(* Enumerable predicates containing elements of any number can be mapped injectively from N *)

Section inf_any_number_to_injection.

  Context {X: Type}.
  Context {p: X -> Prop}.

  Variable E_p: nat -> option X.
  Variable Enum_E_p: enumerator p E_p.

  Variable f: X -> nat.

  Variable D_X: discrete X.

  Variable any_number: forall L, exists x, p x /\ ~ In x L.

  Theorem wo_inj_any_number:
    forall L, {x | p x /\ ~ In x L }.
  Proof.
    intros L.
    pose (E_p' := fun n0 => match E_p n0 with None => None | Some x => if dec_membership D_X L x then None else Some x end).
    apply (wo_enum_sig (fun x => p x /\ ~ In x L) E_p'); intuition.
    intros x. split; unfold E_p'.
    - intros [[n0 H2] % Enum_E_p H1]. exists n0. 
      rewrite H2. destruct dec_membership; intuition.
    - intros [n0 H1]. destruct E_p eqn: E; try discriminate.
      destruct dec_membership; try discriminate.
      inversion H1. repeat rewrite <- H2; intuition.
      + apply Enum_E_p ; intuition. exists n0. now rewrite E, H0. 
      + rewrite H0 in n; firstorder.
  Qed.

  Fixpoint Inj_List n : list X
    := match n with 0 => [] | 
                  S n => let L := Inj_List n in (proj1_sig (wo_inj_any_number L))::L end.

  Lemma Inj_List_spec1:
    forall n1 n2, n1 <= n2 -> incl (Inj_List n1) (Inj_List n2).
  Proof.
    intros n1 n2. induction n2.
    - intros E. assert (n1 = 0) by lia. rewrite H. firstorder.
    - intros E. assert (n1 = S n2 \/ n1 <= n2) by lia. destruct H.
      + rewrite H; firstorder.
      + firstorder. 
  Qed.

  Lemma Inj_List_spec2 n:
    {x | In x (Inj_List (S n)) /\ p x /\ ~ In x (Inj_List n)}.
  Proof.
    exists (proj1_sig (wo_inj_any_number (Inj_List n))).
    split.
    - firstorder.
    - remember (proj2_sig (wo_inj_any_number (Inj_List n))).
      apply a.
  Qed.

  Definition Inj : nat -> X
    := fun n => proj1_sig (Inj_List_spec2 n).

  Lemma Inj_set_injection:
    set_injection (Top nat) p Inj.
  Proof.
    intros n1 n2 _ _ E.
    remember (proj2_sig (Inj_List_spec2 n1)).
    clear Heqa.
    remember (proj2_sig (Inj_List_spec2 n2)).
    clear Heqa0. 
    split. 
    - assert (n1 < n2 \/ n2 < n1 \/ n1 = n2) by lia. destruct H as [H | [H | H]].
      + exfalso. rewrite E in a. 
        apply a0, (Inj_List_spec1 (S n1)).
        * lia.
        * apply a.
      + exfalso. rewrite E in a.
        apply a, (Inj_List_spec1 (S n2)).
        * lia.
        * apply a0.
      + exact H.
    - apply a.
  Qed.
End inf_any_number_to_injection.

Lemma inf_any_number_injection {X} (p: X -> Prop):
  discrete X -> enumerable p -> of_any_number p -> nat_injection p.
Proof.
  intros DX. rewrite of_any_number_iff2.
  intros [E_p Enum_E_p] H. 
  exists (Inj E_p Enum_E_p (fun _ => 0) DX H).
  apply Inj_set_injection.
  exact DX.
Qed.


(* Non-Finite Predicates *) 

Definition finite {X} (p: X -> Prop): Prop
  :=exists L : list X, forall x, p x -> In x L.

Definition strongly_finite {X} (p: X -> Prop): Prop
  :=exists L : list X, forall x, p x <-> In x L.

Lemma notfinite_notstrongly_finite {X} (p: X -> Prop):
  (~ finite p) -> ~ strongly_finite p.
Proof.
  firstorder.
Qed.

Lemma notstrongly_finite_notfinite {X} (p: X -> Prop):
  decidable p -> (~ strongly_finite p) -> ~ finite p.
Proof.
  intros D. assert (stable p) by now apply decidable_stable.
  apply decidable_closure_compl, decidable_agreement in D as [D].
  intros H1. contradict H1.
  destruct H1 as [L H1]. exists (remove_pred (compl p) D L).
  intros x. split.
  - intros px. apply remove_pred_spec1; firstorder.
  - intros H2 % remove_pred_spec2.
    apply H, H2. 
Qed.

Lemma of_any_number_notfinite {X} (p: X -> Prop):
  discrete X -> of_any_number p -> ~ finite p.
Proof.
  intros DX. rewrite of_any_number_iff2.
  intros H1 [L H2]. specialize (H1 L) as [x H1].
  firstorder.
  exact DX. 
Qed. 


(* Characterizations of non-finite predicates *)

Lemma notfinite_iff1 {X} (p: X -> Prop):
  discrete X ->  (~ finite p) <-> (forall L, ~~ exists x, p x /\ ~ In x L). 
Proof.
  intros DX. split.
  - intros H1 L H2. apply H1. 
    exists L. intros x px. 
    destruct (dec_membership DX L x); firstorder.
  - intros H1 [L H2].
    apply (H1 L). intros [x [px H3]]. now apply H3, H2.
Qed.
    
Lemma notfinite_iff2 {X} (p: X -> Prop):
  discrete X -> 
    (~ finite p) <-> (forall n, ~~ exists L : list X, length L = n /\ NoDup L  /\ forall y, In y L -> p y).
Proof.
  intros DX. rewrite notfinite_iff1. 
  split.
  - intros H n. 
    induction n.
    + intros []. exists []. firstorder. econstructor.
    + intros H1. apply IHn. intros (L & H2 & H3 & H4).
      apply (H L). intros [x [H5 H6]]. apply H1.
      exists (x::L). cbn; intuition.
      * now constructor.
      * now rewrite <- H7.
  - intros H L H1.
    apply (H (length L + 1)). 
    intros [L0 H2]. apply H1.
    assert (exists x, In x L0 /\ ~ In x L) as [x H3].
    apply pigeonhole_exists; intuition. lia.
    exists x; intuition.
  - exact DX.
Qed.

Lemma notfinite_iff3 {X} (p: X -> Prop):
  discrete X -> 
    (~ finite p) <-> (forall n, ~~ exists L : list X, n <= length L /\ NoDup L  /\ forall y, In y L -> p y).
Proof.
  intros DX. rewrite notfinite_iff2. 
  split.
  - intros H n.
    rewrite <- of_any_number_iff1_help. apply H.
  - intros H n.
    rewrite of_any_number_iff1_help. apply H.
  - exact DX.
Qed.

Lemma notfinite_iff4 (p: nat -> Prop):
  (~ finite p) <-> (forall n, ~~ exists x, x >= n /\ p x).
Proof.
  rewrite notfinite_iff1. split.
  - intros H1 n H2.
    apply (H1 (seq 0 n)).
    intros [x [px H3]]. 
    apply H2. exists x. rewrite in_seq in H3. intuition. lia.
  - intros H1 L H2.
    apply (H1 (Preliminaries_Lists_Coq.list_max L + 1)). 
    intros [x [H3 px]]. apply H2. exists x. intuition. 
    apply list_max_in in H. lia.
  - exact D_nat.
Qed.


(* Properties of Infinite Predicates with respect to the different Notions *)

(* N is infinite *)

Lemma N_infinite_surj:
  nat_surjection (Top nat).
Proof.  
  exists (fun x => x). intros x. exists x. firstorder.
Qed.

Lemma N_infinite_inj:
  nat_injection (Top nat).
Proof.  
  exists (fun x => x). firstorder.
Qed.

Lemma N_infinite_notfinite:
  ~ finite (Top nat).
Proof.
  apply of_any_number_notfinite, inf_surjection_any_number.
  - exact D_nat.
  - exact N_infinite_surj.
Qed.

(* Infinite Predicates are non-empty *)

Lemma of_any_number_Element {X} (p: X -> Prop):
  of_any_number p -> exists x, p x.
Proof.
  intros H1. specialize (H1 1) as [L H1].
  destruct L; cbn in *; try lia.
  exists x. apply H1; firstorder.
Qed.

Lemma notfinite_weakElement {X} (p: X -> Prop):
  (~ finite p) -> ~~ exists x, p x.
Proof.
  intros H1 H2.
  apply H1. exists nil. intros x px. apply H2. exists x. exact px.
Qed.

(* Infinite Predicates are closed under Supersets *)

Lemma inf_closure_superset_surj {X} (p q: X -> Prop):
  p << q -> nat_surjection p -> nat_surjection q.
Proof.
  intros Sub [f H]. exists f.
  firstorder.
Qed.

Lemma inf_closure_superset_inj {X} (p q: X -> Prop):
  p << q -> nat_injection p -> nat_injection q.
Proof.
  intros Sub [f H]. exists f.
  firstorder.
Qed.

Lemma inf_closure_superset_any_number {X} (p q: X -> Prop):
  p << q -> of_any_number p -> of_any_number q.
Proof.
  intros Sub H n. specialize (H n) as [L H].
  exists L. firstorder.
Qed.

Lemma inf_closure_superset_notfinite {X} (p q: X -> Prop):
  p << q -> (~ finite p) -> ~ finite q.
Proof.
  intros Sub H. contradict H. destruct H as [L Fi].
  exists L. 
  intros x H % Sub.
  apply Fi, H.
Qed. 

(* Infinite Predicates are closed under Surjections *)

Lemma inf_closure_surj_surj {X Y} p q:
  (exists (f: X -> Y), set_surjection p q f) -> nat_surjection q -> nat_surjection p.
Proof.
  intros [f1 H1] [f2 H2].
  exists (fun x => f2 (f1 x)).
  intros n _. 
  specialize (H2 n) as [y H2] ; firstorder.
  specialize (H1 y) as [x H1]; firstorder.
  exists x. intuition. now rewrite H2, H0.
Qed.  

Lemma inf_closure_surj_notfinite {X Y} p q:
  (exists (f: X -> Y), set_surjection p q f) -> (~ finite q) -> ~ finite p.
Proof.
  intros [f H] Infq [L Fi].
  apply Infq. 
  exists (map f L).
  intros y qy. 
  apply H in qy. 
  destruct qy as [x0 [px0 H0]]. 
  rewrite <- H0. 
  apply in_map, Fi, px0.
Qed.

(* Infinite Predicates are closed under Injections *)

Lemma inf_closure_inj_inj {X Y} p q:
  (exists (f: X -> Y), set_injection p q f) -> nat_injection p -> nat_injection q.
Proof.
  intros [f1 H1] [f2 H2].
  exists (fun n => f1 (f2 n)).
  intros n1 n2 _ _ E.
  assert (p (f2 n1)) by now apply (H2 n1 n1). 
  assert (p (f2 n2)) by now apply (H2 n2 n2).
  specialize (H1 (f2 n1) (f2 n2)). 
  specialize (H2 n1 n2). firstorder.
Qed.
 
Lemma inf_closure_inj_any_number {X Y} p q:
  (exists (f: X -> Y), set_injection p q f) -> of_any_number p -> of_any_number q.
Proof.
  intros [f H] H1 n. specialize (H1 n) as [L H1].
  exists (map f L). repeat split.
  - rewrite map_length. intuition.
  - apply (map_setinj_NoDup f p q); intuition.
  - intros y [x [E H3]] % in_map_iff . rewrite <- E. 
    apply (set_inj_spec p q); intuition.
Qed.

Lemma inf_closure_inj_notfinite {X Y} p q:
  discrete X -> discrete Y -> (exists (f: X -> Y), set_injection p q f) -> (~finite p) -> (~finite q).
Proof.
  intros DX DY [f Inj]. 
  rewrite (notfinite_iff2 p DX).
  rewrite (notfinite_iff2 q DY).
  intros H n H1. apply (H n). intros [L H2]. apply H1. 
  exists (map f L). repeat split.
  - rewrite map_length. intuition.
  - apply (map_setinj_NoDup f p q); intuition.
  - intros y [x [E H3]] % in_map_iff. rewrite <- E. 
    apply (set_inj_spec p q); intuition.
Qed.
