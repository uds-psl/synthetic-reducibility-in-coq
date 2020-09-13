(* Summarizing the distinctions of reducibility degrees *)

Require Import Cantor_Pairing_Coq Preliminaries_Coq 
               Definitions_Coq Synthetic_Computability_Theory_Coq 
               Reduction_Characterization_Coq Simple_Predicates_Coq.

(* There exists a simple predicate *)

Theorem Post_Simple_Predicate:
  (exists W, ES W /\ W_SEMIDEC W) -> exists (S: nat -> Prop), simple S.
Proof.
  intros [W [es [W_SDec W_semidec]]].
  destruct (W_full W es) as [c_top c_top_spec].
  exists (S' W W_SDec W_semidec c_top c_top_spec).
  now eapply S_simple.
Qed.


(* One-one and many-one reduction do not coincide on the class of semidecidable, but undecidable predicates *)

Corollary one_red_m_red_distinction:
  (exists W, ES W /\ W_SEMIDEC W) 
    -> exists X Y (p: X -> Prop) (q: Y -> Prop),
        semidec p /\ ~ decidable p /\ semidec q /\ ~ decidable q /\
          ~ (p <=1 q) /\ (p <=m q).
Proof.
  intros W. destruct (Post_Simple_Predicate W) as [S Simple].
  exists (prod nat nat). exists nat. exists (S ** (Top nat)). exists S. repeat split.
  - eapply manyone_red_semidec. 
    + apply many_one_from_prod. 
    + apply Simple.
  - intros H. eapply simple_not_dec. 
    + exact Simple.
    + eapply oneone_red_dec.
      * apply one_one_to_prod.
      * exact H.
  - apply Simple.
  - apply simple_not_dec, Simple.
  - intros H % cyl_iff2. 
    + apply simple_not_cylinder in Simple. intuition.
    + exists nat2_to_nat. apply nat2_to_nat_bij.
  - apply prod_equiv.
Qed.


(* One-one and many-one degrees do not coincide on the class of semidecidable, but undecidable predicates *)

Corollary one_degree_m_degree_distinction:
  (exists W, ES W /\ W_SEMIDEC W) 
    -> exists X Y (p: X -> Prop) (q: Y -> Prop), 
        semidec p /\ ~ decidable p /\ semidec q /\ ~ decidable q /\
          ~ (p =1 q) /\ (p =m q).
Proof.
  intros W. destruct (Post_Simple_Predicate W) as [S Simple].
  exists nat. exists (prod nat nat). exists S. exists (S ** (Top nat)). repeat split.
  - apply Simple.
  - apply simple_not_dec, Simple.
  - eapply manyone_red_semidec. 
    + apply many_one_from_prod. 
    + apply Simple.
  - intros H. eapply simple_not_dec. 
    + exact Simple.
    + eapply oneone_red_dec.
      * apply one_one_to_prod.
      * exact H.
  - intros H % cyl_iff3. 
    + apply simple_not_cylinder in Simple. intuition.
    + exists nat2_to_nat. apply nat2_to_nat_bij.
  - apply prod_equiv.
  - apply prod_equiv.
Qed.


(* Post's Problem with respect to many-one reductions:
    There exists a semidecidable but undecidable predicate, that is not m-complete *)

Corollary Post's_Problem_wrt_Many_One:
  (exists W, ES W /\ W_SEMIDEC W /\ S_M_N' W /\ inhabited (LIST_ID W)) 
     -> exists X (S: X -> Prop), semidec S /\ ~ decidable S /\ ~ m_complete S.
Proof.
  intros (W & es & sdec & smn & [list_id]).
  destruct Post_Simple_Predicate as [S Simple].
  - now exists W.
  - exists nat. exists S; repeat split.
    + apply Simple.
    + apply simple_not_dec, Simple.
    + now apply (simple_not_complete W).
Qed.


(* M-Completeness and TT-Completeness do not coincide *)

Corollary m_completeness_tt_completeness_distinction:
  (exists W, ES W /\ W_SEMIDEC W /\ S_M_N' W /\ inhabited (LIST_ID W)) 
    -> exists X (S: X -> Prop), ~ m_complete S /\ tt_complete S.
Proof.
  intros (W & es & [W_SDec sdec] & smn & [list_id]).
  destruct (W_full W es) as [c_top c_top_spec].
  exists nat. exists (S_Star W W_SDec sdec c_top c_top_spec).
  split.
  - apply (simple_not_complete W); intuition.
    + now exists W_SDec.
    + now apply S_Star_simple.
  - apply (tt_complete_trans (fun '(c,x) => W c x)).
    + exact nat2_nat_iso. 
    + apply tt_red_W_S_Star. 
    + apply m_complete_tt_complete, W_m_complete; intuition. now exists W_SDec.
    + now apply S_Star_simple.
Qed.


(* Many-one and Truth-Table reductions do not coincide on the class of semidecidable, but undecidable predicates *)

Corollary m_red_tt_red_distinction:
  (exists W, ES W /\ W_SEMIDEC W /\ S_M_N' W /\ inhabited (LIST_ID W)) 
    -> exists X Y (p: X -> Prop) (q: Y -> Prop), 
         semidec p /\ ~ decidable p /\ semidec q /\ ~ decidable q /\
           ~ (p <=m q) /\ (p <=tt q). 
Proof. 
  intros (W & es & [W_SDec sdec] & smn & [list_id]).
  destruct (W_full W es) as [c_top c_top_spec].
  exists (prod nat nat). exists nat. 
  exists (fun '(c,x) => W c x). exists (S_Star W W_SDec sdec c_top c_top_spec).
  repeat split.
  - now exists W_SDec.
  - now apply (W_undec W).
  - now apply S_Star_simple.
  - now apply simple_not_dec, S_Star_simple.
  - intros H % many_complete_trans.
    + eapply (simple_not_complete W); intuition.
      * now exists W_SDec.
      * now apply S_Star_simple.
      * exact H. 
    + exact nat2_nat_iso. 
    + apply W_m_complete; intuition. now exists W_SDec.
    + now apply S_Star_simple.
  - apply tt_red_W_S_Star. 
Qed.


(* Many-one and Truth-Table degrees do not coincide on the class of semidecidable, but undecidable predicates *)

Corollary m_degree_tt_degree_distinction:
  (exists W, ES W /\ W_SEMIDEC W /\ S_M_N' W /\ inhabited (LIST_ID W)) 
    -> exists X Y (p: X -> Prop) (q: Y -> Prop), 
         semidec p /\ ~ decidable p /\ semidec q /\ ~ decidable q /\
           ~ (p =m q) /\ (p =tt q). 
Proof. 
  intros (W & es & [W_SDec sdec] & smn & [list_id]).
  destruct (W_full W es) as [c_top c_top_spec].
  exists (prod nat nat). exists nat. 
  exists (fun '(c,x) => W c x). exists (S_Star W W_SDec sdec c_top c_top_spec).
  repeat split.
  - now exists W_SDec.
  - now apply (W_undec W).
  - now apply S_Star_simple.
  - now apply simple_not_dec, S_Star_simple.
  - intros [H % many_complete_trans _].
    + eapply (simple_not_complete W); intuition.
      * now exists W_SDec.
      * now apply S_Star_simple.
      * exact H. 
    + exact nat2_nat_iso. 
    + apply W_m_complete; intuition. now exists W_SDec.
    + now apply S_Star_simple.
  - apply tt_red_W_S_Star.
  - apply W_tt_complete; intuition.
    + now exists W_SDec.
    + exact nat2_nat_iso.
    + exact D_nat.
    + now apply S_Star_simple.
Qed.
