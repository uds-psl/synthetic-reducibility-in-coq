(* Characterizations of Reducibility Notions *)

Require Export List Eqdep_dec.
Import ListNotations.

From Coq Require Import Arith Lia.

Require Import Cantor_Pairing_Coq Preliminaries_Coq Preliminaries_Lists_Coq Definitions_Coq 
               Synthetic_Computability_Theory_Coq Preliminaries_Corresponding_Coq.

(* Many-One Characterization *)

(* Product Predicate *)

Definition product {X Y} p q : X * Y -> Prop 
  := fun t => p (fst t) /\ q (snd t).

Notation "p ** q" := (product p q) (at level 94, no associativity). 

Lemma product_oneone_r {X Y Z} (p: X -> Prop) (q: Y -> Prop) (r: Z -> Prop):
  q <=1 r -> p ** q <=1 p ** r.
Proof.
  intros [f [I H]]. 
  exists (fun '(x,y) => (x, f y)).
  split. 
  - intros [x11 x12] [x21 x22] E.  
    apply pair_equal_spec in E. apply pair_equal_spec. 
    firstorder.
  - intros [x y].
    firstorder.
Qed.

Lemma one_one_to_prod {X} (p: X -> Prop):  
  p <=1 p ** Top X.
Proof.
  exists (fun x => (x,x)).
  split.
  - intros x1 x2 H. apply pair_equal_spec in H. tauto. 
  - intros x. split; firstorder.
Qed.

Lemma many_one_from_prod {X Y} (p: X -> Prop):
   p ** (Top Y) <=m p.
Proof.
  exists fst.
  intros x. split; firstorder.
Qed.

Corollary prod_equiv {X} (p: X -> Prop):
  p =m p ** Top X.
Proof. 
  split. 
  - apply oneone_manyone_inclusion. exact (one_one_to_prod p).
  - exact (many_one_from_prod p).
Qed.


(* Cylinder Predicates *)

Definition cylinder {X} (p:X -> Prop) : Prop
  := exists (q: X -> Prop), p =1 q ** Top X. 

Lemma cyl_iff1 {X} (p: X -> Prop) :
  (exists I: X * X -> X, injective I) 
    -> (cylinder p <-> (forall Y (r: Y -> Prop), (exists I: Y -> X, injective I) -> r <=m p -> r <=1 p)).
Proof.
  intros I1. split.
  - intros [q HB] Y r [I Inj] H1.
    apply (one_one_trans (q ** (Top X))).
    + assert (r <=m q) as [f Hf]. 
      * apply (many_one_trans p); try assumption. 
        apply (many_one_trans (q ** (Top X))); try apply many_one_from_prod.
        apply oneone_manyone_inclusion.
        apply HB.
      * exists (fun x => (f x, I x)). split. 
        intros x1 x2 E. 
        apply pair_equal_spec in E. apply Inj. tauto.
        intros x. split; firstorder.
   + apply HB.
 - intros H1. exists p. split.
    + apply one_one_to_prod.
    + apply H1; intuition. apply many_one_from_prod. 
Qed.

Corollary cyl_iff2 {X} (p: X -> Prop):
  (exists I: X * X -> X, injective I)  -> cylinder p <-> (p ** (Top X) <=1 p).
Proof.
  split.
  - intros H1. apply (cyl_iff1 p); intuition. 
    apply many_one_from_prod. 
  - intros H1. exists p. split; intuition. 
    apply one_one_to_prod.
Qed.

Corollary cyl_iff3 {X} (p: X -> Prop):
  (exists I: X * X -> X, injective I) -> cylinder p <-> (p =1  p ** (Top X)).
Proof.
  split.
  - intros H1 % (cyl_iff2); intuition. 
    split; intuition. 
    apply one_one_to_prod.
  - intros H1.
    exists p.
    split; apply H1. 
Qed.

Lemma prod_cyl {X} (p:X -> Prop):
  (exists I: X * X -> X, injective I) -> cylinder (p ** Top X).
Proof.
  intros [I H]. 
  exists (p ** Top X). split.
  - apply one_one_to_prod.  
  - exists (fun '((x1, x2), pa) => (x1, (I (x2, I pa)))).
    split.
    + intros [[x11 x12] pa1] [[x21 x22] pa2] E. 
      inversion E. apply H in H2. 
      inversion H2. apply H in H4. now rewrite H4.
    + intros [[x1 x2] pa]. firstorder.  
Qed. 


(* Many-One Reduction characterized in terms of One-One Reductions *)

(* Proof by Cylinder Notion *)

Lemma manyone_oneone_iff_Cylinder {X Y} (p: X -> Prop) (q: Y -> Prop):
  (exists (I: X * X -> Y), injective I) -> (exists (I: Y * Y -> Y), injective I) 
    -> p <=m q <-> (p ** (Top X) <=1 q ** (Top Y)).
Proof.
  intros [I Inj] InjY; split. 
  - intros [f H]. apply cyl_iff1.
    + destruct InjY as [IY InjY]. 
      exists (fun '(pa1, pa2) => (IY pa1, IY pa2)).
      intros [pa11 pa12] [pa21 pa22] H1. apply pair_equal_spec. 
      split; apply InjY; now inversion H1.  
    + apply prod_cyl, InjY. 
    + exists (fun pa => (I pa, I pa)).
      intros pa1 pa2 H1. apply Inj. now inversion H1. 
    + exists (fun '(x1, x2) => (f x1, f x2)). 
      intros [x1 x2]. firstorder.
  - intros H % oneone_manyone_inclusion.
    apply (many_one_trans (p ** Top X)). 
    + apply oneone_manyone_inclusion, one_one_to_prod.
    + apply (many_one_trans (q ** Top Y)); intuition.
      apply many_one_from_prod.
Qed.   

(* Proof by explicit Reduction Construction *)

Lemma manyone_oneone_iff {X Y} (p: X -> Prop) (q: Y -> Prop):
  (exists (I: X * X -> Y), injective I) -> p <=m q <-> (p ** (Top X) <=1 q ** (Top Y)).
Proof.
  intros [I H1].
  split.
  - intros [f H]. 
    exists (fun '(x1,x2) => (f x1, I (x1, x2))); split.
    + intros [x11 x12] [x21 x22] H2. 
      apply H1. now inversion H2.
    + intros [x1 x2]. split; firstorder.  
  - intros [f H]. exists (fun x => fst (f (x,x))).
    intros x. split; firstorder.
Qed. 

Lemma manyone_oneone_iff_nat (p: nat -> Prop) (q: nat -> Prop):
  p <=m q <-> (p ** (Top nat) <=1 q ** (Top nat)).
Proof.
  apply manyone_oneone_iff.
  exists nat2_to_nat. apply nat2_to_nat_bij. 
Qed.

(* Characterization transports to computability degree *)

Corollary manyone_oneone_degree_iff {X Y} (p: X -> Prop) (q: Y -> Prop):
  (exists (I: X * X -> Y), injective I) -> (exists (I: Y * Y -> X), injective I)
    -> p =m q <-> (p ** (Top X) =1 q ** (Top Y)).
Proof.
  intros I1 I2.
  split; intros [H1 H2]; split; now apply manyone_oneone_iff.
Qed.

Corollary manyone_oneone_degree_iff_nat (p: nat -> Prop) (q: nat -> Prop):
  p =m q <-> (p ** (Top nat) =1 q ** (Top nat)).
Proof.
  apply manyone_oneone_degree_iff; 
  exists nat2_to_nat; apply nat2_to_nat_bij. 
Qed.

(* Cylinders are the the maximal 1-degreee within a m-degree *)

Corollary cyl_max {X Y}  (p: X -> Prop) (q: Y -> Prop):
  (exists (I: Y * Y -> X), injective I) -> p =m q -> p <=1 q -> q <=1 p ** (Top X).
Proof.
  intros I [_ H1] H2. 
  apply manyone_oneone_iff in H1; intuition. 
  apply (one_one_trans (q ** (Top Y))); intuition.
  exact (one_one_to_prod q).   
Qed. 


(* Truth-Table Characterization *)

(* Truth-Table Cylinders *)

Definition tt_cyl {X} (p : X -> Prop): {LX : list X & forall (LB: list bool), length LB = length LX -> bool} -> Prop
  := fun s => match s with existT _ LX alpha => forall LB H, corresponding p LX LB -> alpha LB H = true end.

Lemma stable_cyl {X} (p: X -> Prop):
  stable (tt_cyl p).
Proof.
  intros [LX alpha] H LB H0 C. 
  destruct alpha eqn: E; trivial.
  exfalso; apply H. intros H1. 
  specialize (H1 LB H0 C).
  rewrite E in H1; discriminate. 
Qed.

(* Proof Irrelevance for Equality Proofs on Nat *)

Lemma PI_equality_nat {n1 n2: nat}:
 forall (H1 H2: n1 = n2), H1 = H2.
Proof.
  apply UIP_dec. 
  intros x y. destruct (D_nat (x,y)); firstorder.
Qed.

(* Basic Properties of Truth-Table Cylinders *)

Lemma tt_cyl_one_one {X} (p: X -> Prop):
  stable p -> p <=1 tt_cyl p.
Proof.
  intros S. 
  exists (fun x => existT _ [x] (fun LB _ => match LB with [b] => b | _ => false end)).
  split.
  - intros x1 x2 H. now inversion H.
  - intros x. split.
    + intros px LB H1 H2. inversion H2.
      inversion H5. apply H3, px. 
    + intros H. cbn in H. apply S. intros npx. 
      enough (false = true) by discriminate.
      specialize (H [false]). intuition. 
      apply H0. constructor. 
      * split; intros H; firstorder.  discriminate.
      * constructor. 
Qed. 

Lemma tt_cyl_tt_red {X} (p: X -> Prop):
  tt_cyl p <=tt p.
Proof.
  apply tt_agree. 
  exists (fun s => match s with existT _ LX alpha => LX end). 
  constructor. 
  intros [LX alpha] LB H. 
  exists (alpha LB H).
  intros H1. cbn. split; intros H2. 
  - firstorder.
  - intros LB0 H0 C. 
    assert (LB = LB0) as <-.
    + apply (corresponding_one_one p LX); intuition. 
    + enough (H = H0) as <- by exact H2.
      apply PI_equality_nat.
Qed. 


(* Embedding of Truth-Table Cylinders *)

Section tt_embeding.

  (* Functional Extensionality for Truth-Table Conditions *)

  Lemma FE_condition n:
    FE -> forall (f1 f2: forall LB: list bool, length LB = n -> bool), (forall LB H, f1 LB H = f2 LB H) -> f1 = f2.
  Proof.
    intros fe f1 f2 H. apply fe.
    intros L. now apply fe.
  Qed. 

  (* Assuming Certain Encodings *)

  Context {Y: Type}.

  Variable (I2: nat -> Y) (H2: injective I2).  
  Variable (IY: Y * Y -> Y) (HY: injective IY).

  Fixpoint list_el_inj {X} (I1: X -> Y) (L: list X): Y
    := match L with nil => I2 0 | x::L => IY (I1 x, list_el_inj I1 L) end.

  Lemma list_el_injective {X} (I1: X -> Y):
     injective I1 -> forall L1 L2, length L1 = length L2 -> list_el_inj I1 L1 = list_el_inj I1 L2 -> L1 = L2.
  Proof.
    intros H1 L1. induction L1; intros L2.
    - destruct L2.  
      + trivial.
      + cbn. lia.
    - destruct L2.
      + cbn; lia.
      + intros E1 E2. specialize (IHL1 L2).
        cbn in E2. apply HY in E2. inversion E2. 
        apply H1 in H0. rewrite H0.
        rewrite IHL1; intuition.
  Qed.

  Lemma injection_ex1 {X}:
     (exists (I: X -> Y), injective I) -> exists I: list X -> Y, injective I.
  Proof.
    intros [I1 H1].
    exists (fun L => IY (I2 (length L), list_el_inj I1 L)).
    intros L1 L2 E. apply HY in E.
    inversion E.
    apply H2 in H0. apply (list_el_injective I1); intuition.
  Qed.

  Fixpoint bool_list_help n : list (list bool)
    := match n with 0 => [[]] | 
                  S n => let LB := bool_list_help n in 
                           (map (fun L => true::L) LB) ++ (map (fun L => false :: L) LB) end. 

  Definition listing : Type -> Type
    := fun X => {L | forall (x: X), In x L}.

  Lemma proof_S_true {n L}:
    length L = n -> length (true::L) = S n.
  Proof.
    cbn; now intros ->.
  Qed.

  Lemma proof_S_false {n L}:
    length L = n -> length (false::L) = S n.
  Proof.
    cbn; now intros ->.
  Qed.

  Lemma bool_list_listing n: listing {LB: list bool & length LB = n}.
  Proof.
    induction n.
    - assert (length (nil: list bool) = 0) by trivial.
      exists [(existT _ [] H)]. intros [LB H0].
      destruct LB. 
      + assert (H = H0) by apply PI_equality_nat.
        rewrite H1; firstorder.
      + cbn in H0; lia.
    - destruct IHn as [L H].
      exists ((map (fun s => match s with existT _ LB H => existT _ (true::LB) (proof_S_true H)end )L)
                ++ (map (fun s => match s with existT _ LB H => existT _ (false::LB) (proof_S_false H)end )L)).
      intros [LB H0]. destruct LB; try (cbn in *; discriminate).
      assert (length LB = n) by (cbn in *; lia). destruct b.
      + apply in_or_app. left. apply in_map_iff.
        exists (existT _ LB H1); split.
        * enough (H0 = proof_S_true H1) as -> by trivial.
            apply PI_equality_nat.
        * apply H.
      + apply in_or_app. right. apply in_map_iff.
        exists (existT _ LB H1); split.
        * enough (H0 = proof_S_false H1) as -> by trivial.
          apply PI_equality_nat.
        * apply H.
  Qed.

  Definition boolL_to_Y (LB: list bool) : Y
    := list_el_inj (fun (b: bool) => if b then I2 1 else I2 0) LB. 

  Lemma injection_ex2 {X}:
    FE -> exists I: forall (LX: list X), (forall LB : list bool, length LB = length LX -> bool) -> Y, 
          forall LX, forall alpha1 alpha2, I LX alpha1 = I LX alpha2 -> alpha1 = alpha2 .
  Proof.
    intros fe.
    exists (fun LX alpha => boolL_to_Y (map (fun s => match s with existT _ LB HB => alpha LB HB end) (proj1_sig (bool_list_listing (length LX))))).
    intros LX alpha1 alpha2 E.
    apply FE_condition; intuition. 
    remember (proj2_sig (bool_list_listing (length LX))). 
    apply list_el_injective in E; intuition.
    - rewrite map_ext_in_iff in E.
      specialize (E (existT _ LB H)). cbn in *. apply E. 
      apply (map_inj_elem (fun s : {LB : list bool & length LB = length LX} => let (LB, _) := s in LB)).
      + intros [LB1 HL1] [LB2 HL2] E1.
        revert HL1 HL2. rewrite E1. intros HL1 HL2. 
        enough (HL1 = HL2) as <- by trivial.
        apply PI_equality_nat. 
      + clear Heqi. specialize (i (existT _ LB H)).
        apply in_map_iff. exists (existT _ LB H); intuition.
    - intros b1 b2.
      destruct b1, b2; intros E1 % H2; firstorder; discriminate.
    - now repeat rewrite map_length. 
  Qed.

  (* Final Embedding *)

  Lemma injection_ex {X}:
    FE -> (exists (I: X -> Y), injective I) 
      -> exists I : {LX : list X & forall LB : list bool, length LB = length LX -> bool} -> Y, injective I.
  Proof.
    intros fe I1.
    remember (injection_ex1 I1). 
    remember (@injection_ex2 X fe).
    clear Heqe Heqe0 I1. destruct e as [IL1 H1]. destruct e0 as [ITT HTT].
    exists (fun s => match s with existT _ LX alpha => IY ((IL1 LX), (ITT LX alpha)) end).
    intros [L1 alpha1] [L2 alpha2] E. apply HY in E. inversion E.
    apply H1 in H0. 
    revert H3 E. revert alpha1. 
    rewrite H0.
    intros alpha1 H3 E. 
    apply HTT in H3. now rewrite H3. 
  Qed.

End tt_embeding.


(* Characterization on Truth-Table Reductions in terms of One-One Reductions *)

Lemma tt_oneone_iff_help {X Y} (p: X -> Prop) (q: Y -> Prop):
  stable p -> (exists I: X -> Y, injective I) -> p <=tt q -> p <=1 tt_cyl q.
Proof.
  intros S [I HI] [f [H0]] % tt_agree.
  assert (forall x, forall L : list bool, length L = length (I x :: f x) -> {b : bool | corresponding q (I x :: f x) L -> p x <-> b = true}).
  - intros x L H. destruct L; cbn in H. 
    + discriminate.
    + destruct (H0 x L).
      * lia.
      * exists x0. intros C. 
        apply i. now inversion C.
  - exists (fun x => existT _ (I x :: f x) (fun LB H => proj1_sig (X0 x LB H))).
    split.
    + intros x1 x2 E. inversion E. now apply HI.
    + intros x. split.
      * intros px LB H. destruct (X0 x LB H).
        cbn ; firstorder.
      * intros H. apply S.
        intros npx. apply (corresponding_weak q (I x :: f x)). 
        intros [LB [C Le]]. apply npx. specialize (H LB Le C).
        now apply (proj2_sig (X0 x LB Le) C).
Qed.

Lemma tt_oneone_iff1 {X Y} (p: X -> Prop) (q: Y -> Prop):
 FE -> (exists (I: X -> Y), injective I) -> (exists I: nat -> Y, injective I) -> (exists I: Y * Y -> Y, injective I)
    -> p <=tt q -> (tt_cyl p <=1  tt_cyl q).
Proof.
  intros fe I1 [I2 H2] [IY HY] H. assert (tt_cyl p <=tt q).
  - eapply tt_trans.
    + apply tt_cyl_tt_red.
    + exact H.
  - apply tt_oneone_iff_help.
    + apply stable_cyl.
    + now (apply (injection_ex I2 H2 IY HY)).  
    + apply H0.
Qed. 

Lemma tt_oneone_iff2 {X Y} (p: X -> Prop) (q: Y -> Prop):
  stable p -> (tt_cyl p <=1 tt_cyl q) -> p <=tt q.
Proof.
  intros S H. apply (tt_trans (tt_cyl q)).
  - apply manyone_tt_inclusion, oneone_manyone_inclusion. 
    apply (one_one_trans (tt_cyl p)). 
    + apply tt_cyl_one_one, S.
    + exact H. 
  - apply tt_cyl_tt_red.
Qed.

Theorem tt_oneone_iff {X Y} (p: X -> Prop) (q: Y -> Prop):
  FE -> stable p 
    -> (exists (I: X -> Y), injective I) -> (exists I: nat -> Y, injective I) -> (exists I: Y * Y -> Y, injective I)
       -> p <=tt q <-> ((tt_cyl p) <=1 (tt_cyl q)).
Proof.
  intros Sp; split.
  - now apply tt_oneone_iff1.
  - now apply tt_oneone_iff2.
Qed.

Theorem tt_oneone_iff_nat (p: nat -> Prop) (q: nat -> Prop):
  FE -> stable p -> p <=tt q <-> ((tt_cyl p) <=1 (tt_cyl q)).
Proof.
  intros fe S. apply tt_oneone_iff; intuition.
  - now exists (fun x => x).
  - now exists (fun x => x).
  - exists nat2_to_nat. apply nat2_to_nat_bij. 
Qed.

(* Characterization transports to computability degree *)

Corollary tt_oneone_degree_iff {X Y} (p: X -> Prop) (q: Y -> Prop):
  FE -> stable p -> stable q 
    -> (exists (I: X -> Y), injective I) -> (exists I: nat -> Y, injective I) -> (exists I: Y * Y -> Y, injective I)
    -> (exists (I: Y -> X), injective I) -> (exists I: nat -> X, injective I) -> (exists I: X * X -> X, injective I)
       -> p =tt q <-> ((tt_cyl p) =1 (tt_cyl q)).
Proof.
  intros fe sp sq I1 I2 I3 I4 I5 I6.
  split; intros [H1 H2]; split; now apply tt_oneone_iff.
Qed.

Corollary tt_oneone_degree_iff_nat (p: nat -> Prop) (q: nat -> Prop):
  FE -> stable p -> stable q 
    -> p =tt q <-> ((tt_cyl p) =1 (tt_cyl q)).
Proof.
  intros fe sp sq. 
  split; intros [H1 H2]; split; now apply tt_oneone_iff_nat.
Qed. 

(* TT-Cylinders are the the maximal 1-degreee within a tt-degree *)

Corollary tt_cyl_max {X Y}  (p: X -> Prop) (q: Y -> Prop):
  FE -> stable q -> 
    (exists (I: Y -> X), injective I) -> (exists I: nat -> X, injective I) -> (exists I: X * X -> X, injective I)
       -> p =tt q -> p <=1 q -> q <=1 tt_cyl p.
Proof.
  intros fe S I1 I2 I3 [_ H1] H2. 
  apply tt_oneone_iff in H1; try assumption.
  apply (one_one_trans (tt_cyl q)); intuition. 
  now apply tt_cyl_one_one.
Qed. 



