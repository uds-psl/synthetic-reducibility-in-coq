(* Basic Synthetic Reducibility Results, Synthetic Computability Axioms *)

Require Export List.
Import ListNotations.

From Coq Require Import Arith Lia.

Require Import Cantor_Pairing_Coq Preliminaries_Coq Preliminaries_Lists_Coq 
               Definitions_Coq Recursive_Mu_Operator_Coq Preliminaries_Corresponding_Coq.

(* Basic Properties of Decidability *) 

Definition decidable_char {X} (p: X -> Prop): Prop
  := inhabited (dec_pred p).
 
Lemma decidable_agreement {X} (p: X -> Prop):
  decidable p <-> decidable_char p.
Proof.
  split. 
  - intros [F H]. 
    constructor. 
    intros x. specialize (H x).
    destruct (F x) eqn: H1.
    + left. apply H. trivial.
    + right. intros H2. apply H in H2. discriminate. 
  - intros [D].
    exists (fun x => if D x then true else false).
    intros x. destruct (D x).
    + tauto.
    + split. tauto. intro H. discriminate.
Qed.

Lemma decidable_stable {X} (p: X -> Prop):
  decidable p -> stable p.
Proof.
  intros [D] % decidable_agreement x nnpx. 
  destruct (D x); firstorder.
Qed.

Lemma decidable_closure_compl {X} (p: X -> Prop):
  decidable p -> decidable (compl p).
Proof.
  repeat rewrite decidable_agreement. 
  intros [D]. constructor. intros x. firstorder.
Qed.

Lemma decidable_closure_conj {X} (p: X -> Prop) (q: X -> Prop):
  decidable p -> decidable q -> decidable (fun x => p x /\ q x).
Proof.
  repeat rewrite decidable_agreement.
  intros [D1] [D2]. constructor. firstorder.
Qed.

Lemma decidable_closure_disj {X} (p: X -> Prop) (q: X -> Prop):
  decidable p -> decidable q -> decidable (fun x => p x \/ q x).
Proof.
  repeat rewrite decidable_agreement.
  intros [D1] [D2]. constructor. firstorder.
Qed.


(* Basic Properties of Semidecidability, (Strong-) Enumerability *)

Lemma semidec_dec {X} (p: X -> Prop):
  decidable p -> semidec p.
Proof.
  intros [F H]. 
  exists ( fun y n => F y).
  intros x. 
  specialize (H x). 
  split.
  - intros px % H. exists 0. exact px.
  - intros [_ fx % H]. exact fx. 
Qed.

Definition enum_To_StrongenumF {X} (F: nat -> option X) x0: nat -> X
  := fun n => match F n with Some x => x | None => x0 end.

Lemma enum_To_Strongenum_spec {X} (p: X -> Prop) F x0:
  enumerator p F -> p x0 -> strong_enumerator p (enum_To_StrongenumF F x0).
Proof.
  intros H1 H2 x.
  split; unfold enum_To_StrongenumF.
  - intros [n px] % H1.
    exists n.  rewrite px. trivial. 
  - intros [n px]. destruct (F n) eqn: E. 
    + apply H1. exists n. rewrite <- px. exact E.
    + rewrite <- px. exact H2.
Qed.
  
Lemma enum_To_Strongenum {X} (p: X -> Prop):
  (exists x, p x) -> enumerable p -> strong_enumerable p.
Proof.
  intros [x px] [E H].
  exists (enum_To_StrongenumF E x). 
  now apply enum_To_Strongenum_spec.
Qed.

Definition Strongenum_To_enumF {X} (F: nat -> X): nat -> option X
  := fun n => Some (F n).

Lemma enum_To_enumOpt_spec {X} (p: X -> Prop) F:
  strong_enumerator p F -> enumerator p (Strongenum_To_enumF F).
Proof.
  intros H x.
  split; unfold Strongenum_To_enumF.
  - intros [n H1] % H. exists n. rewrite H1. trivial. 
  - intros [n H1]. apply H. exists n. inversion H1. trivial.
Qed.

Lemma Strongenum_To_enum {X} (p: X -> Prop):
  strong_enumerable p -> enumerable p.
Proof.
  intros [E H]. exists (Strongenum_To_enumF E). now apply enum_To_enumOpt_spec.
Qed.

Definition semidec_To_enumF {X} (F: X -> nat -> bool) (Sur: nat -> X * nat) : nat -> option X
  := fun n => let (x,n) := Sur n in 
                    if F x n then Some x else None.

Lemma semidec_To_enum_spec {X} (p: X -> Prop) F Sur:
  surjective Sur -> semidecider p F ->  enumerator p (semidec_To_enumF F Sur).
Proof.
  intros S H x. split; unfold semidec_To_enumF.
  - intros [n px] % H. specialize (S (x,n)) as [n0 H1].
    exists n0. rewrite H1, px. trivial.
  - intros [n H1]. apply H.
    destruct (Sur n). destruct (F x0 n0) eqn: E.
    + exists n0. inversion H1. rewrite <- H2. exact E.
    + discriminate.
Qed.

Lemma semidec_To_enum {X} (p: X -> Prop):
  enumerable_T X -> semidec p -> enumerable p.
Proof.
  intros EX [SDec H].
  assert (enumerable_T (X * nat)) as [Sur H1]. 
  - apply enumerable_closure_pair. 
    + exact EX.
    + exists (fun n => n). intros n. eauto. 
  - exists (semidec_To_enumF SDec Sur).
  now apply semidec_To_enum_spec.
Qed.

Definition enum_To_semidecF {X} (D: discrete X) (F: nat -> option X) : X -> nat -> bool
  := fun x n => match F n with Some x0 => if D (x,x0) then true else false |
                                None => false end.

Lemma enum_To_semidec_spec {X} (p: X -> Prop) D F:
  enumerator p F -> semidecider p (enum_To_semidecF D F).
Proof.
  intros H x.
  split; unfold enum_To_semidecF.
  - intros [n H1] % H.
    exists n. rewrite H1. destruct (D (x,x)); firstorder.
  - intros [n H1]. apply H. exists n.
    destruct (F n). 
    + destruct (D (x,x0)). rewrite e. trivial. discriminate. 
    + discriminate. 
Qed. 

Lemma enum_To_semidec {X} (p: X -> Prop):
  discrete X -> enumerable p -> semidec p.
Proof.
  intros D [E H2].
  exists (enum_To_semidecF D E).
  now apply enum_To_semidec_spec.
Qed.

Lemma semidec_enum_datatype {X} (p: X -> Prop):
  datatype X -> semidec p <-> enumerable p.
Proof.
  intros [EX [D]].
  split.
  - now apply semidec_To_enum.
  - now apply enum_To_semidec. 
Qed.


(* Closures of Semidecidability *)

Fixpoint f_mono (f: nat -> bool) n: bool
  := match n with 0 => f 0 | S n => orb (f (S n)) (f_mono f n) end.

Lemma f_mono_spec1 f n:
  f n = true -> forall m, n <= m -> f_mono f m = true.
Proof.
  intros H m. induction m; cbn. 
  - intros H1. assert (n = 0) by lia. now rewrite H0 in H. 
  - intros H1. assert (n = S m \/ n <= m) by lia. destruct H0.
    + now rewrite <- H0, H.  
    + apply IHm in H0. rewrite H0; now destruct (f (S m)).
Qed.

Lemma f_mono_spec2 f n:
  f_mono f n = true -> exists n0, f n0 = true.
Proof.
  induction n; cbn.
  - intros H. now exists 0.
  - intros H. apply Bool.orb_prop in H as [H | H].
    + now exists (S n). 
    + apply IHn, H. 
Qed. 

Lemma semidec_closure_conj {X} (p: X -> Prop) (q: X -> Prop):
  semidec p -> semidec q -> semidec (fun x => p x /\ q x).
Proof.
  intros [F1 H1] [F2 H2].
  exists (fun x n => andb (f_mono (F1 x) n) (f_mono (F2 x) n)).
  intros x; split.
  - intros [[n1 px] % H1 [n2 qx] % H2].
    exists (max n1 n2). 
    remember (f_mono_spec1 (F1 x) n1 px (max n1 n2)). clear Heqe. 
    specialize (e (Nat.le_max_l n1 n2)).
    remember (f_mono_spec1 (F2 x) n2 qx (max n1 n2)). clear Heqe0.
    specialize (e0 (Nat.le_max_r n1 n2)).
    now rewrite e,e0.
  - intros [n H]. 
    assert (true = (f_mono (F1 x) n && f_mono (F2 x) n)%bool) by firstorder.
    apply Bool.andb_true_eq in H0 as [H0 H0'].
    split. 
    + now apply H1, (f_mono_spec2 (F1 x) n).
    + now apply H2, (f_mono_spec2 (F2 x) n). 
Qed. 

Lemma semidec_closure_disj {X} (p: X -> Prop) (q: X -> Prop):
  semidec p -> semidec q -> semidec (fun x => p x \/ q x).
Proof.
  intros [F1 H1] [F2 H2].
  exists (fun x n => orb (F1 x n) (F2 x n)).
  intros x; split.
  - intros [[n px] % H1| [n qx] % H2]; exists n. 
    + now rewrite px.
    + rewrite qx. now destruct F1. 
  - intros [n H]. destruct F1 eqn: F1n.
    + left. apply H1. exists n; firstorder. 
    + destruct F2 eqn: F2n.
      * right. apply H2. exists n; firstorder. 
      * cbn in H; discriminate. 
Qed.

Lemma semidec_closure_ex {X} (p: nat -> X -> Prop):
  semidec (fun pa => p (fst pa) (snd pa)) -> semidec (fun x => exists n, p n x).
Proof.
  intros [F H]. 
  exists (fun x n => let (n1, n2) := nat_to_nat2 n in F (n1, x) n2).
  intros x. split; intros [n H1]. 
  - specialize (H (n, x)). 
    apply H in H1 as [n0 H1]. 
    assert (exists n1, nat_to_nat2 n1 = (n, n0)) as [n1 H2] by apply nat_to_nat2_bij.
    exists n1. now rewrite H2.
  - destruct nat_to_nat2. specialize (H (n0, x)). exists n0. apply H. now exists n1. 
Qed.


(* Basic Properties of Reductions *)

Lemma oneone_manyone_inclusion {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=1 q -> p <=m q.
Proof.
  intros [f [_ H]].
  exists f. 
  exact H.
Qed.
 
Lemma manyone_tt_inclusion {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=m q -> p <=tt q.
Proof.
  intros [f H].
  exists (fun x => [f x]).
  exists (fun _ L _ => match L with nil => false | (b::br) => b end). 
  intros x L H1 H2. inversion H2. rewrite <- H4. apply H.
Qed.

Lemma one_one_refl {X} (p: X -> Prop):
  p <=1 p.
Proof.
  exists (fun x => x); firstorder. 
Qed.

Lemma one_one_trans {X Y Z} {p: X -> Prop} (q: Z -> Prop){r: Y -> Prop} :
  (p <=1 q) -> (q <=1 r) -> (p <=1 r).
Proof.
  intros [f1 [I1 H1]] [f2 [I2 H2]].
  exists (fun x => f2 (f1 x)). split.
  - apply composition_inj. exact I1. exact I2.
  - intros x. 
    specialize (H1 x).
    specialize (H2 (f1 x)).
    tauto.
Qed.

Lemma one_one_red_compl {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=1 q -> (compl p) <=1 (compl q).
Proof.
  intros [f H].
  exists f.
  firstorder.
Qed.

Lemma many_one_refl {X} (p: X -> Prop):
  p <=m p.
Proof.
  exists (fun x => x); firstorder. 
Qed.

Lemma many_one_trans {X Y Z} {p: X -> Prop} (q: Z -> Prop) {r: Y -> Prop} :
  (p <=m q) -> (q <=m r) -> (p <=m r).
Proof.
  intros [f1 H1] [f2 H2].
  exists (fun x => f2 (f1 x)). 
  intros x. 
  specialize (H1 x).
  specialize (H2 (f1 x)).
  tauto.
Qed.

Lemma many_one_red_compl {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=m q -> (compl p) <=m (compl q).
Proof.
  intros [f H].
  exists f.
  firstorder.
Qed.

Definition tt_red_char {X Y} p q : Prop
  := exists (f: X -> list Y),
      inhabited (forall x L (H: length L = length (f x)), {b | corresponding q (f x) L -> p x <-> b = true}).

Lemma tt_agree {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=tt q <-> tt_red_char p q.
Proof.
  split. 
  - intros [f [alpha T]]. 
    exists f. constructor. intros x L H. 
    exists (alpha x L H). firstorder.   
  - intros [f [T]].  
    exists f. exists (fun x L H => proj1_sig (T x L H)).
    intros x L H. exact (proj2_sig (T x L H)). 
Qed.

Lemma tt_refl {X} (p: X -> Prop): 
  p <=tt p.
Proof.
  exists (fun x => [x]).
  exists (fun _ L _ => match L with nil => false | (b::br) => b end). 
  intros x L H1 H2. now inversion H2.
Qed.


(* Technical Proof for the Transitivity of Thruth-Table Reductions *)

Definition tt_map {Y Z} {f2: Y -> list Z} (alpha2: forall y (LB: list bool), length LB = length (f2 y) -> bool) LLB
  := map (fun s => match s with existT _ y (existT _ LB H) => alpha2 y LB H end) LLB.

Theorem unconcat {Y Z: Type} {q r} {f: Y -> list Z} {alpha} (LY: list Y) (LLZ: list (list Z)) (LB: list bool):
   (forall (x : Y) (L : list bool) (H : length L = length (f x)),
         corresponding r (f x) L -> q x <-> alpha x L H = true)
    -> length LY = length LLZ -> length LB = length (concat LLZ) -> (map (@length Z) LLZ = map (fun y => length (f y)) LY)
    -> {LLB: list {y & {LB : list bool & length LB = length (f y)}} & 
    (length LLB = length LLZ) /\
        (corresponding r (concat (map f LY)) LB 
              -> corresponding q LY (tt_map alpha LLB))
          }.
Proof.
  revert LY LB. induction LLZ; intros LY LB HTT E1 E2 E3; destruct LY; cbn in E1; try discriminate.
  - exists nil. intuition; constructor. 
  - specialize (IHLLZ LY (skipn (length a) LB)). 
    assert (length LY = length LLZ) by lia.
    apply IHLLZ in H as (LLB & H1 & H2); intuition.
    assert (length (firstn (length a) LB) = length (f y)).
    { cbn in E3. inversion E3. rewrite H0. apply firstn_length_le. 
      rewrite <- H0, E2. cbn. rewrite app_length. lia. }
    exists ( (existT _ y (existT _ (firstn (length a) LB) H )) :: LLB); cbn.
    + rewrite H1; intuition. cbn; constructor.
      * apply HTT. rewrite <- (firstn_skipn (length a)) in H0. 
        apply corresponding_firstn in H0; intuition.
      * apply H2. rewrite <- (firstn_skipn (length a)) in H0. 
        apply corresponding_skipn in H0; intuition.
    + cbn in E2. rewrite app_length in E2.
      rewrite skipn_length, E2. lia. 
    + cbn in E3. now inversion E3. 
Qed.

Lemma tt_trans {X Y Z} {p: X -> Prop} (q: Y -> Prop) {r: Z -> Prop} :
  (p <=tt q) -> (q <=tt r) -> (p <=tt r).
Proof.
  intros [f1 [H1]] % tt_agree.   intros [f2 [alpha2 H2]]. repeat rewrite tt_agree.  
  exists (fun x => concat (map f2 (f1 x))).
  constructor. 
  intros x LB H2'. specialize (H1 x).  
  assert (length (f1 x) = length (map f2 (f1 x))) as H1' by now rewrite map_length.
  assert (map (@length Z) (map f2 (f1 x)) = map (fun y => length (f2 y)) (f1 x)) as H3' by now rewrite map_map.
  destruct (unconcat (f1 x) (map f2 (f1 x)) LB H2 H1' H2' H3') as [LLB [HLLB1 HLLB2]].  
  destruct (H1 (tt_map alpha2 LLB)) as [b Hb].
  { unfold tt_map. now rewrite map_length, HLLB1 , map_length. }
  exists b.
  intros C. apply Hb.
  now apply HLLB2. 
Qed.


(* Truth-Table Properties concerning complements; require at some points stability *)

Lemma tt_red_to_compl {X} (p: X -> Prop):
  stable p -> p <=tt (compl p).
Proof.
  intros S. 
  exists (fun x => [x]).
  exists (fun _ L _ => match L with nil => false | (b::br) => negb b end).
  intros x L H1 H2. inversion H2.
  destruct y; firstorder.
  - cbn in *; discriminate.
  - apply S. intros npx % H3. discriminate.
Qed. 

Lemma tt_red_from_compl {X} (p: X -> Prop):
  (compl p) <=tt p.
Proof.
  exists (fun x => [x]).
  exists (fun _ L _ => match L with nil => false | (b::br) => negb b end).
  intros x L H1 H2. inversion H2.
  destruct y; firstorder.
  - cbn in *; discriminate.
  - intros px % H3. discriminate.
Qed. 

Lemma tt_red_compl1 {X Y} (p: X -> Prop) (q: Y -> Prop):
  stable p -> (compl p) <=tt (compl q) -> p <=tt q.
Proof.
  repeat rewrite tt_agree. intros S [f [TT]].
  exists f.
  constructor. intros x L H.
  destruct (TT x (map negb L)).
  - now rewrite map_length.
  - exists (negb x0). 
    intros C % corresponding_compl1 % i. split.
    + intros npx. destruct x0; firstorder.
    + intros E. apply S. intros npx % C.
      rewrite npx in E; cbn in E; discriminate.
Qed.

Lemma tt_red_compl2 {X Y} (p: X -> Prop) (q: Y -> Prop):
  stable q -> p <=tt q -> (compl p) <=tt (compl q).
Proof.
  repeat rewrite tt_agree. intros S [f [TT]].
  exists f.
  constructor. intros x L H.
  destruct (TT x (map negb L)).
  - now rewrite map_length.
  - exists (negb x0). 
    intros C % corresponding_compl2 % i. split.
    + intros npx. destruct x0; firstorder.
    + intros E. intros npx % C. 
      rewrite npx in E; cbn in E; discriminate.
    + exact S.
Qed. 


(* Transport of Decidability and Semidecidability *)

Lemma manyone_red_dec {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=m q -> decidable q -> decidable p.
Proof.
  intros [f R] [F D]. exists (fun x => F (f x)). 
  intros x. destruct (D (f x)); firstorder. 
Qed.

Lemma manyone_red_semidec {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=m q -> semidec q -> semidec p.
Proof.
  intros [f R] [F S].
  exists (fun x => F (f x)).
  intros x.
  specialize (R x).
  specialize (S (f x)). tauto.
Qed.

Corollary oneone_red_dec {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=1 q -> decidable q -> decidable p.
Proof.
  intros H % oneone_manyone_inclusion. revert H. exact (manyone_red_dec p q).
Qed.

Corollary oneone_red_semidec {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=1 q -> semidec q -> semidec p.
Proof.
  intros H % oneone_manyone_inclusion. revert H. exact (manyone_red_semidec p q).
Qed.

Lemma tt_red_dec {X Y} (p: X -> Prop) (q: Y -> Prop):
  p <=tt q -> decidable q -> decidable p.
Proof.
  intros [f [T]] % tt_agree [F d].
  apply decidable_agreement. constructor.
  intros x. specialize (T x (map F (f x))). rewrite map_length in T. intuition.
  assert (corresponding q (f x) (map F (f x))).  
  - clear H. induction (f x). 
    + constructor.  
    + cbn; constructor; firstorder.
  - destruct H as [[|] H].
    + left. apply H; intuition.
    + right. intros px % H; intuition.
Qed.


(*Upper Semi Lattice by join predicate *)
 
Definition join {X Y} p q : X + Y -> Prop
  := fun xy => match xy with inl x => p x | inr x => q x end.


(* Upper Semi Latice Many One *)

Lemma join_redm_l {X Y} (p: X -> Prop) (q: Y -> Prop) :
  p <=m join p q.
Proof.
  exists (fun x => inl x).
  intros x. tauto.
Qed.

Lemma join_redm_r {X Y} (p: X -> Prop) (q: Y -> Prop) :
  q <=m join p q.
Proof.
  exists (fun x => inr x).
  intros x. tauto.
Qed.

Lemma lub_m_join {X Y Z} (p: X -> Prop) (q: Y -> Prop):
  forall (r: Z -> Prop), (p <=m r) -> (q <=m r) -> join p q <=m r.
Proof.
  intros r [f1 H1] [f2 H2].
  exists (fun d => match d with inl x => f1 x | inr y => f2 y end).
  intros [x | y]; cbn.
  - exact (H1 x).
  - exact (H2 y).
Qed.  

(* Upper Semi Latice TT *)

Lemma join_redtt_l {X Y} (p: X -> Prop) (q: Y -> Prop) :
  p <=tt join p q.
Proof.
  apply manyone_tt_inclusion, join_redm_l.
Qed.

Lemma join_redtt_r {X Y} (p: X -> Prop) (q: Y -> Prop) :
  q <=tt join p q.
Proof.
  apply manyone_tt_inclusion, join_redm_r.
Qed.

Lemma lub_tt_join {X Y Z} (p: X -> Prop) (q: Y -> Prop):
  forall (r: Z -> Prop), (p <=tt r) -> (q <=tt r) -> join p q <=tt r.
Proof.
  intros r [f1 [alpha1 T1]] [f2 [alpha2 T2]].
  apply tt_agree. exists (fun d => match d with inl x => f1 x | inr y => f2 y end).
  constructor. 
  intros [x | y] L H.
  - exists (alpha1 x L H).
    firstorder. 
  - exists (alpha2 y L H).
    firstorder. 
Qed. 


(* Basic Properties of Computability Degrees *)

Lemma rec_iso_refl {X} (p: X -> Prop):
  p == p.
Proof.
  exists (fun x => x). intuition.
  split. 
  - firstorder.
  - intros x. exists x; firstorder.
Qed.

Lemma rec_iso_sym {X Y} (p: X -> Prop) (q: Y -> Prop):
  enumerable_T X -> discrete Y -> p == q -> q == p.
Proof.
  intros [E HE] DY [f [b H]].
  exists (inv DY E HE f b).
  split.
  - exact (inv_bij DY E HE f b).
  - intros x. 
    specialize (H (inv DY E HE f b x)). unfold inv in H.     
    rewrite (proj2 (inv_spec DY E HE f b)) in H.
    firstorder.
Qed.

Lemma rec_iso_trans {X Y Z} {p: X -> Prop} (q: Z -> Prop){r: Y -> Prop} :
  (p == q) -> (q == r) -> (p == r).
Proof.
  intros [f1 [[I1 S1] H1]] [f2 [[I2 S2] H2]].
  exists (fun x => f2 (f1 x)). split.
  - split.  
    + now apply composition_inj. 
    + now apply composition_sur.
  - firstorder.
Qed.

Lemma one_one_deg_refl {X} (p: X -> Prop):
  p =1 p.
Proof. 
  split; apply one_one_refl. 
Qed.

Lemma one_one_deg_trans  {X Y Z} {p: X -> Prop} (q: Z -> Prop){r: Y -> Prop} :
  (p =1 q) -> (q =1 r) -> (p =1 r).
Proof.
  intros [H1 H2] [H3 H4]. 
  split; now apply (one_one_trans q).
Qed.

Lemma many_one_deg_refl {X} (p: X -> Prop):
  p =m p.
Proof. 
   split; apply many_one_refl. 
Qed.

Lemma many_one_deg_trans  {X Y Z} {p: X -> Prop} (q: Z -> Prop){r: Y -> Prop} :
  (p =m q) -> (q =m r) -> (p =m r).
Proof.
  intros [H1 H2] [H3 H4]. 
  split; now apply (many_one_trans q).
Qed.

Lemma tt_deg_refl {X} (p: X -> Prop):
  p =tt p.
Proof. 
  split; apply tt_refl. 
Qed.

Lemma tt_deg_trans  {X Y Z} {p: X -> Prop} (q: Z -> Prop){r: Y -> Prop} :
  (p =tt q) -> (q =tt r) -> (p =tt r).
Proof.
  intros [H1 H2] [H3 H4]. 
  split; now apply (tt_trans q).
Qed.

Lemma rec_iso_one_one {X Y} (p: X -> Prop) (q: Y -> Prop): 
  p == q -> p <=1 q.
Proof.
  intros [f H]. exists f. split; apply H.
Qed. 

Lemma rec_iso_one_one_deg {X Y} (p: X -> Prop) (q: Y -> Prop): 
  enumerable_T X -> discrete Y -> p == q -> p =1 q.
Proof.
  intros E D H. split. 
  - now apply rec_iso_one_one.  
  - apply rec_iso_one_one. now apply rec_iso_sym.
Qed.

Lemma one_one_many_one_deg {X Y} (p: X -> Prop) (q: Y -> Prop): 
  p =1 q -> p =m q.
Proof.
  intros [H1 H2]. split; now apply oneone_manyone_inclusion.
Qed.

Lemma many_one_tt_deg {X Y} (p: X -> Prop) (q: Y -> Prop): 
  p =m q -> p =tt q.
Proof.
  intros [H1 H2]. split; now apply manyone_tt_inclusion.
Qed.


(* Completeness Properties *)

Lemma one_complete_trans {X Y} (p: X -> Prop) (q: Y -> Prop):
  type_iso X Y -> p <=1 q -> one_complete p -> semidec q -> one_complete q.
Proof.
  intros I H1 H2 H3.
  split.
  - exact H3. 
  - intros Z IZ DZ p0 H4. apply (one_one_trans p).
    + apply H2; intuition. eapply iso_trans.
      * exact I.
      * exact IZ. 
    + exact H1.
Qed.  

Lemma many_complete_trans {X Y} (p: X -> Prop) (q: Y -> Prop):
  type_iso X Y -> p <=m q -> m_complete p -> semidec q -> m_complete q.
Proof.
  intros I H1 [_ H2] H3.
  split.
  - exact H3. 
  - intros Z IZ DZ p0 H4. apply (many_one_trans p).
    + apply H2; intuition. eapply iso_trans.
      * exact I.
      * exact IZ. 
    + exact H1.
Qed. 

Lemma tt_complete_trans {X Y} (p: X -> Prop) (q: Y -> Prop):
  type_iso X Y -> p <=tt q -> tt_complete p -> semidec q -> tt_complete q.
Proof.
  intros I H1 [_ H2] H3.
  split.
  - exact H3. 
  - intros Z IZ DZ p0 H4. apply (tt_trans p).
    + apply H2; intuition. eapply iso_trans.
      * exact I.
      * exact IZ. 
    + exact H1.
Qed.

Lemma one_complete_m_complete {X} (p: X -> Prop):
  one_complete p -> m_complete p.
Proof.
  intros [H1 H2].
  split. 
  - exact H1.
  - intros Y IZ DY q Sq. 
    apply oneone_manyone_inclusion. apply H2; intuition.
Qed. 

Lemma m_complete_tt_complete {X} (p: X -> Prop):
  m_complete p -> tt_complete p.
Proof.
  intros [H1 H2].
  split. 
  - exact H1.
  - intros Y IZ DY q Sq. 
    apply manyone_tt_inclusion. apply H2; intuition.
Qed.


(* Properties of the Synthetic Computability Axioms *)

Section Axioms.

  (* Assuming an enumerator of semidecidable predicates W *)
  
  Variable W: nat -> nat -> Prop.

  Definition W0 : nat -> Prop
    := fun n =>  W n n.
  
  Lemma W_empty: (ES W) -> exists c_bot, forall x, ~ W c_bot x.
  Proof.
    intros es. 
    assert (semidec (fun (n: nat) => False)).
    - exists (fun _ _ => false). 
      intros x. firstorder. discriminate.
    - apply es in H as [c H]. exists c. firstorder.
  Qed.

  Lemma W_full: (ES W) -> exists c_top, forall x, W c_top x.
  Proof.
    intros es.
    assert (semidec (fun (n: nat) => True)).
    - exists (fun _ _ => true). firstorder.
    - apply es in H as [c H]. exists c. firstorder.
  Qed.

  Lemma red_W0_W:
    W0 <=1 (fun '(c,x) => W c x).
  Proof.
    exists (fun n => (n,n)). 
    split. 
    - intros n1 n2 E % pair_equal_spec. firstorder.
    - firstorder.
  Qed.

  Lemma W0_notCoRE: 
    (ES W) -> ~ semidec (compl W0).
  Proof.
    intros es [c H] % es.
    specialize (H c).
    firstorder.
  Qed.
  
  Lemma W0_undec:
    (ES W) -> ~ decidable W0.
  Proof. 
    intros es d % decidable_closure_compl % semidec_dec. 
    now apply W0_notCoRE.
  Qed.

  Corollary W_notCoRE: 
    (ES W) -> ~ semidec (compl (fun '(c,x) => W c x)).
  Proof.
    intros es H % (oneone_red_semidec (compl W0) (compl (fun '(c,x) => W c x))).
    - now apply W0_notCoRE. 
    - apply one_one_red_compl, red_W0_W.
  Qed.

  Lemma W_undec:
    (ES W) -> ~ decidable (fun '(c,x) => W c x).
  Proof. 
    intros es d % decidable_closure_compl % semidec_dec.
    now apply W_notCoRE.
  Qed.

  Corollary W0_semidec:
    (W_SEMIDEC W) -> semidec W0.
  Proof.
    intros WSDec. apply (oneone_red_semidec W0 (fun '(c,x) => W c x)).
    - exact red_W0_W.
    - assumption.
  Qed. 

  Lemma W_one_complete:
    (ES W) -> (W_SEMIDEC W) -> one_complete (fun '(c,x) => W c x).
  Proof.
    intros es W_semidec. split. 
    - exact W_semidec.
    - intros Y [f1 [_ Sur]] DY q [F H].
      set (f1' := fun n => f1 (nat_to_nat2 n)).
      assert (surjective f1').
      { intros y. destruct (Sur y). destruct ((proj2 nat_to_nat2_bij) x).
        exists x0. unfold f1'. now rewrite H1, H0. }
      set (f2 := Right_Inv_N DY f1' H0).
      assert (semidec (fun x => q (f1' x))). 
      + exists (fun x n => F (f1' x) n); firstorder.
      + apply es in H1 as [c H1].
        exists (fun y => (c,  f2 y)). split.
        * intros y1 y2 E. inversion E. now apply Right_Inv_inj_N in H3.
        * intros y. split; unfold f2, Right_Inv_N.
          ** intros qy. apply H1. 
             now rewrite (Right_Inv_spec_N DY f1' H0). 
          ** intros Wy % H1. 
             now rewrite (Right_Inv_spec_N DY f1' H0) in Wy. 
  Qed.

  Lemma W_m_complete:
    (ES W) -> (W_SEMIDEC W) -> m_complete (fun '(c,x) => W c x).
  Proof.
    intros es W_semidec.
    now apply one_complete_m_complete, W_one_complete.
  Qed.

  Lemma W_tt_complete:
    (ES W) -> (W_SEMIDEC W) -> tt_complete (fun '(c,x) => W c x).
  Proof.
    intros es W_semidec. 
    now apply m_complete_tt_complete, W_m_complete.
  Qed.

  Corollary one_complete_iff {X} (q: X -> Prop):
    (ES W) -> (W_SEMIDEC W) -> type_iso nat X -> discrete X -> semidec q  
      -> ((fun '(c,x) => W c x) <=1 q) <-> one_complete q.
  Proof.
    intros es W_SDec I H D. 
    assert (type_iso (nat*nat) X). 
    { eapply iso_trans. 
        - exact nat2_nat_iso.
        - exact I.
    } 
    split.
    - intros H1. apply (one_complete_trans (fun '(c,x) => W c x)); intuition.
      now apply W_one_complete.
    - intros H1. apply H1.
      + apply datatype_iso_inv; try apply nat2_datatype; intuition.
      + exact D_nat2. 
      + assumption. 
  Qed.

  Corollary m_complete_iff {X} (q: X -> Prop):
    (ES W) -> (W_SEMIDEC W) -> type_iso nat X -> discrete X -> semidec q  
      -> ((fun '(c,x) => W c x) <=m q) <-> m_complete q.
  Proof.
    intros es W_SDec I H D. 
    assert (type_iso (nat*nat) X). 
    { eapply iso_trans. 
        - exact nat2_nat_iso.
        - exact I.
    } 
    split.
    - intros H1. apply (many_complete_trans (fun '(c,x) => W c x)); intuition.
      now apply W_m_complete.
    - intros H1. apply H1.
      + apply datatype_iso_inv; try apply nat2_datatype; intuition.
      + exact D_nat2. 
      + assumption. 
  Qed.

  Corollary tt_complete_iff {X} (q: X -> Prop):
    (ES W) -> (W_SEMIDEC W) -> type_iso nat X -> discrete X -> semidec q  
      -> ((fun '(c,x) => W c x) <=tt q) <-> tt_complete q.
  Proof.
    intros es W_SDec I H D. 
    assert (type_iso (nat*nat) X). 
    { eapply iso_trans. 
        - exact nat2_nat_iso.
        - exact I.
    } 
    split.
    - intros H1. apply (tt_complete_trans (fun '(c,x) => W c x)); intuition.
      now apply W_tt_complete.
    - intros H1. apply H1.
      + apply datatype_iso_inv; try apply nat2_datatype; intuition.
      + exact D_nat2. 
      + assumption. 
  Qed.


  (* CNS-Operator implies the computability of list-indices *)

  Lemma CNS_to_LIST_ID:
    (CNS_sig W) -> {c_bot | forall x, ~ W c_bot x} -> (LIST_ID W).
  Proof.
    intros [cns H] [c_bot H1] L. induction L.
    - exists c_bot; firstorder.
    - destruct IHL as [c IHL]. 
      exists (cns a c).
      apply H, IHL.
  Qed.

End Axioms. 

(* Minimization-Operator for enumerable Predicates is inconsistent with synthetic axioms *) 

Section Inconsistent_Mu.
  Variable mu_enum_strong: forall (p : nat -> Prop) f,
      enumerator p f -> ex p -> 
        {n | p n /\ forall y, p y -> y >= n }.

  Theorem dec_range0: 
    decidable (fun (f: nat -> nat) => exists x, f x = 0).
  Proof. 
    apply decidable_agreement. constructor.
    intros f. 
    specialize (mu_enum_strong (fun y => exists n, f n = y) (fun n => Some (f n))).
    assert (enumerator (fun y : nat => exists n : nat, f n = y)
                     (fun n : nat => Some (f n))).
    - intros y. split; firstorder; eauto. 
      exists x. now inversion H.  
    - apply mu_enum_strong in H.
      + destruct H as [[| n] H].
        * left. exact (proj1 H).
        * right. intros [n1 H1].
        destruct H as [_ H].  
        enough (0 >= S n) by lia.  
        apply (H 0). now exists n1.
      + exists (f 0). eauto.
  Qed.

  Theorem dec_tsat: 
    decidable (fun (f: nat -> bool) => exists n, f n = true).
  Proof.
    apply (manyone_red_dec (fun (f: nat -> bool) => exists n, f n = true) 
        (fun (f: nat -> nat) => exists x, f x = 0)). 
    - exists (fun (f: nat -> bool) => fun n => if (f n) then 0 else 1).
      intros f.
      split.
      + intros [x H]. exists x. rewrite H. trivial.  
      + intros [x H]. exists x. destruct (f x); firstorder; discriminate.
    - apply dec_range0. 
  Qed.

  Theorem mu_enum_strong_inconsistent {X} (p: X -> Prop):
    semidec p -> decidable p.
  Proof. 
    intros [F H].
    destruct dec_tsat as [d H1]. 
    exists (fun x => d (F x)).
    intros x. specialize (H x). firstorder.
  Qed.

End Inconsistent_Mu.