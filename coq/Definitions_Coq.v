Require Import Preliminaries_Coq Preliminaries_Lists_Coq.

(* Main Synthetic Computability Theory Definitions used in the Thesis *)

(*Decidability, Semidecidability, (Strong) Enumerability *)

Definition decidable {X} (p: X -> Prop) : Prop
  := exists F, forall x, p x <-> F x = true.

Definition stable {X} (p: X -> Prop) : Prop
  := forall x, ~~ p x -> p x.

Definition semidecider {X} (p: X -> Prop) (F: X -> nat -> bool): Prop
  := forall x, p x <-> exists n, F x n = true.

Definition semidec {X} (p: X -> Prop): Prop
  := exists F, semidecider p F.

Definition enumerator {X} (p: X -> Prop) (F: nat -> option X): Prop
  := forall x, p x <-> exists n, F n = Some x.

Definition strong_enumerator {X} (p: X -> Prop) (F: nat -> X): Prop
  := forall x, p x <-> exists n, F n = x.

Definition enumerable {X} (p: X -> Prop): Prop
  := exists F, enumerator p F.

Definition strong_enumerable {X} (p: X -> Prop): Prop
  := exists F, strong_enumerator p F.


(*Reductions*)

Definition one_one_redfunc {X Y} p q (f: X -> Y) : Prop
  := injective f /\ forall x, p x <-> q (f x).

Definition one_one_red {X Y} p q : Prop
  := exists (f: X -> Y) , one_one_redfunc p q f.

Notation "p <=1 q" := (one_one_red p q) (at level 95, no associativity).

Definition many_one_redfunc {X Y: Type} p q (f: X -> Y) : Prop
  := forall x, p x <-> q (f x).

Definition many_one_red {X Y} p q : Prop
  := exists (f: X -> Y), many_one_redfunc p q f.

Notation "p <=m q" := (many_one_red p q) (at level 95, no associativity).

Definition corresponding {X} (p: X -> Prop) LX LB: Prop
  := Forall2 (fun x b => p x <-> b = true) LX LB. 
 
Definition tt_red {X Y} p q : Prop
  := exists (f: X -> list Y), exists (alpha: forall x L, length L = length (f x) -> bool),
      forall x L H, corresponding q (f x) L -> p x <-> alpha x L H = true.

Notation "p <=tt q" := (tt_red p q) (at level 95, no associativity).

(* Computability Degrees *)

Definition rec_iso {X Y} p q: Prop
  :=exists (f: X -> Y), bijective f /\ forall x, p x <-> q (f x).

Notation "p == q" := (rec_iso p q) (at level 95, no associativity). 

Definition one_one_degree {X Y} (p: X -> Prop) (q: Y -> Prop): Prop
  := (p <=1 q) /\ (q <=1 p).

Notation "p =1 q" := (one_one_degree p q) (at level 95, no associativity).

Definition many_one_degree {X Y} (p: X -> Prop) (q: Y -> Prop): Prop
  := (p <=m q) /\ (q <=m p).

Notation "p =m q" := (many_one_degree p q) (at level 95, no associativity).

Definition tt_degree {X Y} (p: X -> Prop) (q: Y -> Prop): Prop
  := (p <=tt q) /\ (q <=tt p).

Notation "p =tt q" := (tt_degree p q) (at level 95, no associativity).


(* Reduction Completeness *)

Definition one_complete {X} (p: X -> Prop) : Prop
  := semidec p /\ forall Y, type_iso X Y -> discrete Y 
                   -> forall (q: Y -> Prop), semidec q -> q <=1 p.

Definition m_complete {X} (p: X -> Prop) : Prop
  := semidec p /\ forall Y, type_iso X Y -> discrete Y 
                   -> forall (q: Y -> Prop), semidec q -> q <=m p.

Definition tt_complete {X} (p: X -> Prop) : Prop
  := semidec p /\ forall Y, type_iso X Y -> discrete Y 
                   -> forall (q: Y -> Prop), semidec q -> q <=tt p.

Definition FE : Prop
  := forall X (T: X -> Type) (f1 f2: forall (x: X), T x), (forall x, f1 x = f2 x) -> f1 = f2.


(* Axioms based on the enumerator of semidecidable predicates W *)

Section Axioms.

  Definition ES_SIG : Type
    := {W: nat -> nat -> Prop | forall (p: nat -> Prop), semidec p <-> exists c, forall x, W c x <-> p x}.

  Variable W: nat -> nat -> Prop.

  Definition ES : Prop
   := forall (p: nat -> Prop), semidec p <-> exists c, forall x, W c x <-> p x.

  Definition W_SEMIDEC : Prop
    := semidec (fun '(c,x) => W c x).

  Definition S_M_N' : Prop
    := forall (f: nat -> nat), exists (k: nat -> nat), forall (c: nat) x, (W (k c)) x <-> W c (f x).

  Definition CNS_sig : Type
    := {cns | forall n L, (forall x, W n x <-> In x L) 
         -> forall m x, W (cns m n) x <-> In x (m :: L)}.

  Definition LIST_ID : Type
    := forall (L : list nat), {c | forall x, W c x <-> In x L}.

End Axioms.

