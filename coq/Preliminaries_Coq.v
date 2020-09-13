(* Preliminary Tactics, Definitions, Notations, and Results *)

Require Import Cantor_Pairing_Coq.

(* Tactics *)

Lemma FalseDec_help (P : Prop):
  ~(~ (P \/ ~P)).
Proof.
  firstorder. 
Qed. 

Ltac FalseDec p :=
  let x := fresh "H" in 
    apply (FalseDec_help p); intros [x | x].


(* Injectivity, Surjectivity, Bijectivity of Functions *)

Definition injective {X Y} (f: X -> Y): Prop 
  := forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition surjective {X Y} (f: X -> Y): Prop 
  := forall x2, exists x1, f x1 = x2.

Definition bijective {X Y} (f: X -> Y): Prop 
  := injective f /\ surjective f.

Definition set_surjection {X Y} (p: X -> Prop) (q: Y -> Prop) (f: X -> Y): Prop
  := forall y, q y -> exists x, p x /\ f x = y.

Definition set_injection {X Y} (p: X -> Prop) (q: Y -> Prop) (f: X -> Y): Prop
  := forall x1 x2, p x1 -> p x2 -> f x1 = f x2 -> x1 = x2 /\ q (f x1).

Lemma set_inj_spec {X Y} (p: X -> Prop) (q: Y -> Prop) (f: X -> Y):
  set_injection p q f -> forall x, p x -> q (f x).
Proof.
  intros H x px.
  specialize (H x x).
  firstorder.
Qed. 

Lemma composition_inj {X Y Z} (f1: X -> Y) (f2: Y -> Z):
  injective f1 -> injective f2 -> injective (fun x => f2 (f1 x)).
Proof.
  intros H1 H2 x1 x2 H.
  specialize (H1 x1 x2).
  specialize (H2 (f1 x1) (f1 x2)).
  tauto.
Qed.

Lemma composition_sur {X Y Z} (f1: X -> Y) (f2: Y -> Z):
  surjective f1 -> surjective f2 -> surjective (fun x => f2 (f1 x)).
Proof.
  intros H1 H2 z. 
  specialize (H2 z) as [y H2].
  specialize (H1 y) as [x H1].
  exists x. rewrite H1, H2. trivial.
Qed.

Lemma composition_bij {X Y Z} (f1: X -> Y) (f2: Y -> Z):
  bijective f1 -> bijective f2 -> bijective (fun x => f2 (f1 x)).
Proof.
  intros [I1 S1] [I2 S2]. split.
  - apply composition_inj; intuition.
  - apply composition_sur; intuition.
Qed.


(* Type isomorphism *)

Definition type_iso X Y: Prop
  :=exists (f: X -> Y), bijective f.

Lemma type_iso_refl X: 
  type_iso X X.
Proof.
  exists (fun x => x). split. 
  - intros x1 x2 E. firstorder.
  - intros y. exists y. firstorder.
Qed.

Lemma iso_trans X Y Z:
  type_iso X Y -> type_iso Y Z -> type_iso X Z.
Proof.
  intros [f1 H1] [f2 H2].
  exists (fun x => (f2 (f1 x))).
  now apply composition_bij.
Qed.

Lemma iso_product_product {X}:
  type_iso (X*X) X -> type_iso ((X*X)*(X*X)) (X*X).
Proof.
  intros [IS [I S]]. exists (fun '(x,y) => (IS x, IS y)). split. 
  - intros [x11 x12] [x21 x22] E.
    apply pair_equal_spec in E. apply pair_equal_spec.  firstorder.
  - intros [y1 y2]. 
    destruct (S y1) as [x1 H1]. 
    destruct (S y2) as [x2 H2].
    exists (x1, x2).
    rewrite H1,H2. trivial.
Qed.


(* Corollaries out of Cantor *)

Corollary nat_to_nat2_bij : bijective nat_to_nat2.
Proof.
  split.
  - intros n1 n2 H. 
    rewrite <- (nat2_to_nat_nat_to_nat2_cancel n1), <- (nat2_to_nat_nat_to_nat2_cancel n2).
    now rewrite H.
  - intros c. rewrite <- (nat_to_nat2_nat2_to_nat_cancel c).  
    eauto.
Qed.

Corollary nat_nat2_iso:
  type_iso nat (nat * nat).
Proof.
  exists nat_to_nat2. 
  exact nat_to_nat2_bij.
Qed.

Corollary nat2_to_nat_bij : bijective nat2_to_nat.
Proof.
  split.
  - intros c1 c2 H. 
    rewrite <- (nat_to_nat2_nat2_to_nat_cancel c1), <- (nat_to_nat2_nat2_to_nat_cancel c2).
    now rewrite H.
  - intros n. rewrite <- (nat2_to_nat_nat_to_nat2_cancel n).  
    eauto.
Qed.

Corollary nat2_nat_iso: 
  type_iso (nat * nat) nat.
Proof.
  exists nat2_to_nat.
  exact nat2_to_nat_bij.
Qed.
    
(* Basic Notions regarding Predicates *)

Definition compl {X} (p: X -> Prop) : X -> Prop
  := fun x => ~ (p x).

Definition setminus {X} (p: X -> Prop) (q: X -> Prop): X -> Prop
  := fun x => p x /\ ~ q x.

Notation "p \ q" := (setminus p q) (at level 95, no associativity). 

Definition subset {X} (p: X -> Prop) (q: X -> Prop): Prop
  := forall x, p x -> q x.

Notation "p << q" := (subset p q) (at level 95, no associativity). 

Definition range {X Y} (f : X -> Y) (p: Y -> Prop): Y -> Prop
  := fun y => exists x, f x = y. 

Definition Top X: X -> Prop
  := fun n => True.


(* Certifying Decider, Discreteness, Enumerable Types, Datatypes *)

Definition dec (P: Prop) : Type 
  := {P} + {~ P}.

Definition dec_pred {X} (p: X -> Prop): Type
  := forall x, dec (p x).

Definition discrete (X: Type): Type 
  := dec_pred (fun '(x,y) => x = y :> X).

Lemma discrete_closure_pair {X Y}:
  discrete X -> discrete Y -> discrete (X * Y).
Proof.
  intros DX DY [[x1 y1] [x2 y2]]. 
  destruct (DX (x1,x2)), (DY (y1, y2)).
  left. rewrite e,e0. trivial.
  all: right; intros H % pair_equal_spec; intuition. 
Qed.

Lemma D_nat: discrete nat.
Proof.
  intros [x y]. unfold dec. decide equality.
Defined.

Lemma D_nat2: discrete (nat*nat).
Proof.
  apply discrete_closure_pair; exact D_nat.
Qed.

Definition enumerable_T X : Prop
  := exists (F: nat -> X), surjective F. 

Lemma enumerable_closure_pair {X Y}:
  enumerable_T X -> enumerable_T Y -> enumerable_T (X * Y).
Proof.
  intros [E1 H1] [E2 H2].
  exists (fun n => let '(n1, n2) := nat_to_nat2 n in (E1 n1, E2 n2)).
  assert (surjective nat_to_nat2) by apply nat_to_nat2_bij.
  intros [x y]. 
  specialize (H1 x) as [n1 H1]. specialize (H2 y) as [n2 H2].
  specialize (H (n1, n2)) as [n H]. 
  exists n. now rewrite H, H1, H2. 
Qed.  

Definition datatype (X: Type) : Prop
  := enumerable_T X /\ inhabited (discrete X).

Lemma datatype_closure_pair {X Y}:
  datatype X -> datatype Y -> datatype (X * Y).
Proof.  
  intros [EX [DX]] [EY [DY]]. 
  split.
  - now apply enumerable_closure_pair.
  - constructor. now apply discrete_closure_pair.
Qed. 

Lemma nat_datatype: datatype nat.
Proof.
  split.
  - exists (fun n => n). intros n. eauto. 
  - constructor. exact D_nat. 
Qed.

Lemma nat2_datatype: datatype (nat * nat).
Proof.
  apply datatype_closure_pair; apply nat_datatype.
Qed. 
