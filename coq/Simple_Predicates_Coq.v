(* Simple Predicates, Construction of Simple Predicates S and S*, Properties of Simple Predicates *)

Require Export List.
Import ListNotations.

From Coq Require Import Arith Lia.

Require Import Cantor_Pairing_Coq Preliminaries_Coq Preliminaries_Lists_Coq Preliminaries_Corresponding_Coq
               Definitions_Coq Recursive_Mu_Operator_Coq Synthetic_Computability_Theory_Coq
               Reduction_Characterization_Coq Infinite_Predicates_Coq.


(* Existence of Simple Predicates contradictory when defined via injections *)

Definition simple_strong {X} (p: X -> Prop) : Prop
  := semidec p /\ nat_injection (compl p) /\
     forall (q: X -> Prop), nat_injection q -> semidec q -> ~ (q << (compl p)).

Lemma simple_strong_contradiction:
  ~ (exists X (p: X -> Prop), inhabited (discrete X) /\ simple_strong p) .
Proof.
  intros [X [p [[DX] S]]]. 
  destruct S as [H1 [[f H2] H3]].
  specialize (H3 (fun x => exists n, f n = x)).
  apply H3.
  - exists f. intros n1 n2 _ _. firstorder. eauto.
  - exists (fun x n => if DX (f n, x) then true else false).
    intros x; split; intros [n H]; exists n; destruct DX; firstorder. 
    discriminate.
  - intros x [n H]. rewrite <- H.
    specialize (H2 n n). firstorder.
Qed.


(* Infinite defined as not finite *)

Definition infinite {X} (p: X -> Prop) : Prop
  := ~ finite p.

Definition simple {X} (p: X -> Prop) : Prop
  := semidec p /\ infinite (compl p) /\
      forall (q: X -> Prop), infinite q -> semidec q -> ~ (q << (compl p)).

Lemma simple_not_dec {X} (p: X -> Prop) :
  simple p -> ~ decidable p.
Proof.
  intros [_ [H2 H3]] De.
  specialize (H3 (compl p)).
  assert ((compl p) << (compl p)) by exact (fun x S => S).
  exact (H3 H2 (semidec_dec (compl p) (decidable_closure_compl p De)) H) .
Qed.

(* Simple Predicates are no cylinders *)

Lemma simple_not_cylinder (p: nat -> Prop):
  simple p -> ~ cylinder p.
Proof.
  intros [SDec [Inf Im]] [f1 [Inf1 C]] % cyl_iff2.
  - apply notfinite_weakElement in Inf.
    apply Inf. intros [x0 npx].
    specialize (Im (fun x => (exists n, x = f1 (x0, n)))).
    apply Im.
    + eapply (inf_closure_inj_notfinite (fun '(x,_) => x = x0) _ D_nat2 D_nat).
      * exists f1. intros [x11 x12] [x21 x22] E1 E2 E3. 
        intuition. rewrite E1. eauto.
      * apply of_any_number_notfinite, inf_surjection_any_number. exact D_nat2.
        exists (fun '(_,y) => y).
        intros n. exists (x0,n). intuition.
    + exists (fun x n => if D_nat (x, f1 (x0, n)) then true else false).
      intros x. split. 
      * intros [n E]. destruct (D_nat (x, f1 (x0, n))) eqn: E1.
        ** exists n. setoid_rewrite E1. trivial.
        ** firstorder.
      * intros [n E]. destruct (D_nat (x, f1 (x0, n))) eqn: E1. 
        ** exists n. exact e.
        ** discriminate.
    + intros x  [n ->] [H _] % C.
      cbn in H. firstorder. 
  - exists nat2_to_nat. apply nat2_to_nat_bij. 
Qed.


(* Construction and Verification of Post's Simple Predicate S *)

Section Simple_Predicate_S.

  (* Assuming enumerator of semidecidable predicates W and its semidecidability *)

  Variable W : nat -> nat -> Prop. 
  Variable es : ES W.

  Variable W_SDec: nat * nat -> nat -> bool.
  Variable W_semidecider: semidecider (fun '(c,x) => W c x) W_SDec.

  Variable c_top : nat.
  Variable c_top_spec: forall x, W c_top x.

  (* Auxiliary Predicate C *)

  Definition C : (nat*nat) -> Prop
    := fun '(c,x) => W c x /\ x > 2*c.

  Lemma C_nonempty: 
    C (c_top, 1 + 2 * c_top).
  Proof.
    split.
    - apply c_top_spec.
    - lia.
  Qed.

  Definition C_SDec: (nat*nat) -> nat -> bool
    := fun '(c,x) n => andb (W_SDec (c,x) n) (2*c <? x).

  Lemma C_semidecider:
    semidecider C C_SDec.
  Proof.
    intros [c x].
    split.
    - intros [Wcx E]. 
      apply (W_semidecider(c,x)) in Wcx as [n Wcx].
      exists n. 
      apply leb_correct_conv in E. unfold C_SDec. rewrite Nat.ltb_antisym, Wcx, E. firstorder.
    - intros [n Ccx]. 
      apply RelationClasses.eq_Symmetric, Bool.andb_true_eq in Ccx as [H1 H2].
      split.
      + apply (W_semidecider (c,x)). exists n. firstorder.
      + apply leb_complete_conv. 
        rewrite Nat.leb_antisym. 
        rewrite <- H2. firstorder.
  Qed.

  Definition iso_three_nat_func : nat -> (nat * nat) * nat
    := fun n => let (n1, n2) := nat_to_nat2 n in (nat_to_nat2 n1, n2). 

  Lemma iso_three_nat_func_spec:
    surjective iso_three_nat_func.
  Proof.
    intros [[n1 n2] n3].
    remember (proj2 nat_to_nat2_bij).
    destruct (s (n1, n2)) as [n0 H1].
    destruct (s (n0, n3)) as [n00 H2].
    exists n00. unfold iso_three_nat_func. now rewrite H2, H1.
  Qed.  

  Definition C_Enum: nat -> nat * nat
    := enum_To_StrongenumF (semidec_To_enumF C_SDec iso_three_nat_func) (c_top, 1 + 2 * c_top).

  Lemma C_enumerator:
    strong_enumerator C C_Enum.
  Proof.
    apply enum_To_Strongenum_spec.
    - apply semidec_To_enum_spec.
      + exact iso_three_nat_func_spec.
      + exact C_semidecider. 
    - exact C_nonempty.
  Qed.

  Definition DomC : nat -> Prop
    := fun c => exists x, C (c,x).

  Lemma DomC_nonempty: DomC c_top.
  Proof.
    exists (1+2*c_top).
    exact C_nonempty.
  Qed.

  Definition DomC_Enum : nat -> nat
    := fun n => fst (C_Enum n).

  Lemma DomC_enumerator:
    strong_enumerator DomC DomC_Enum.
  Proof.
    intros c; split; unfold DomC_Enum.
    - intros [x H]. apply C_enumerator in H as [n H]. 
      exists n. rewrite H. trivial.
    - intros [n H]. exists (snd (C_Enum n)). rewrite <- H.
      apply C_enumerator. exists n. apply surjective_pairing.   
  Qed.   
    
  Definition RangeC c : nat -> Prop
    := fun x => C(c,x).

  Definition RangeC_Enum c : nat -> option nat
    := fun n => match C_Enum n with (c1,x) => if D_nat (c,c1) then Some x else None end.

  Lemma RangeC_Enum_spec c:
    enumerator (RangeC c) (RangeC_Enum c).
  Proof.
    intros x. split.
    - intros Ccx. unfold RangeC in Ccx. apply C_enumerator in Ccx as [n Ccx].
      exists n. unfold RangeC_Enum. rewrite Ccx. 
      destruct (D_nat (c, c)); firstorder.
    - intros [n H]. apply C_enumerator.
      exists n. unfold RangeC_Enum in H.
      destruct (C_Enum n) as [c1 x1]. 
      destruct (D_nat (c, c1)). 
      + rewrite e. now inversion H.
      + discriminate. 
  Qed.

  (* Definition of psi via recursive mu-operator for enumerable predicates *)

  Definition psi: forall c, DomC c -> nat .
  Proof.
    intros c H. 
    apply (mu_enum (fun x => C (c,x)) (RangeC_Enum c)).
    - apply RangeC_Enum_spec.
    - exact H.
  Defined.

  Lemma psi_spec c H:
     C (c,psi c H).
  Proof. 
    eapply (mu_enum_spec (fun x => C (c,x))).
  Qed.

  Lemma psi_spec1 c H:
    psi c H > 2*c.
  Proof.
    exact (proj2 (psi_spec c H)).
  Qed.

  Lemma psi_PI c H1 H2:
    psi c H1 = psi c H2.
  Proof.
    apply (constant_mu_enum (fun x => C (c, x)) (RangeC_Enum c)
    (RangeC_Enum_spec c) H1 H2).
  Qed.

  (* Definition of the simple predicate S as the range of psi *)

  Definition S : nat -> Prop 
    := fun x => exists c H, psi c H = x.


  (* S is semidecidable *)

  Definition DomC_proof n: DomC (DomC_Enum n).
  Proof.
    apply DomC_enumerator.
    eauto.
  Qed.

  Definition S_Enum : nat -> nat
    := fun n => let c := DomC_Enum n in 
                  let H := DomC_proof n in 
                     psi c H.

  Lemma S_enumerator:
    strong_enumerator S S_Enum.
  Proof.
    intros x.
    split.
    - intros [c [H E]].
      assert (exists n, DomC_Enum n = c) as [n H1]. 
      apply DomC_enumerator. exact H.
      exists n. unfold S_Enum. 
      revert E. revert H. rewrite <- H1. intros H E.
      rewrite <- E.
      exact (psi_PI (DomC_Enum n) (DomC_proof n) H).
    - intros [n H]. 
      unfold S_Enum in H.
      exists (DomC_Enum n).
      exists (DomC_proof n).
      exact H.
  Qed.  

  Corollary S_SemiDec:
    semidec S.
  Proof.
    apply semidec_enum_datatype. 
    - exact nat_datatype.
    - apply Strongenum_To_enum. exists S_Enum. exact S_enumerator.
  Qed.


  (* Complement of S contains no semidecidable, infinite subset *)
   
  Lemma S_No_S_Inf_Subset:
    forall (q: nat -> Prop), infinite q -> semidec q -> ~ (q << (compl S)).
  Proof.
    intros q Inf [c Se] % es H.
    apply Inf.
    exists (seq 0 (1+2*c)).
    intros x qx.
    assert (x <= 2*c). 
    - destruct (Nat.le_gt_cases x (2*c)). 
      + exact H0. 
      + exfalso. 
        assert (exists x, C (c,x)). 
        * exists x. split. apply Se, qx. exact H0.
        * assert (exists x0, q x0 /\ S x0) as [x0 [qx0 Sx0]].
          { exists (psi c H1). split.
            - apply Se. apply psi_spec.
            - exists c. exists H1. trivial.
          }
          apply (H x0 qx0), Sx0. 
    - apply in_seq. lia.
  Qed.


  (* Co-Infinity Proof of S *)

  Lemma DomC_pullback n L:
    (forall x, In x L -> S x /\ x <= 2 * n) -> forall x, In x L
      -> exists c H, psi c H = x /\ c < n.
  Proof. 
    intros H1 x [[c [H Sx]] E] % H1.
    exists c. exists H. intuition. rewrite <- Sx in E. 
    assert (psi c H > 2 * c) by apply psi_spec1.
    lia.
  Qed.

  Lemma DomC_pullback_list n L:
    NoDup L -> (forall x, In x L -> S x /\ x <= 2 * n) -> 
      exists (LC: list nat), NoDup LC /\ length LC = length L /\
        forall c, In c LC -> exists H, In (psi c H) L /\ c < n.
  Proof.
    intros ND Sub.
    induction L.
    - exists nil.
      intuition. contradiction H. 
    - remember (DomC_pullback n (a::L) Sub a).
      assert (In a (a::L)) as H0 by intuition .
      apply e in H0 as [c0 [H0 [E1 E2]]].
      assert (NoDup L) by (inversion ND; intuition).
      apply IHL in H as [LC H].
      exists (c0::LC).
      intuition.
      + constructor. intros In. apply H3 in In as [H0' E]. 
        assert (a = psi c0 H0') by (rewrite <- E1; exact (psi_PI c0 H0 H0')).
        rewrite <- H2 in E. inversion ND. intuition. exact H1.
      + cbn. rewrite H. trivial.
      + destruct H2.
        * rewrite <- H2.  exists H0. rewrite E1. intuition.
        * apply H3 in H2 as [H4 E]. exists H4. intuition.
      + intros y In1. assert (In y (a::L)) by intuition.
        apply Sub in H1. exact H1.    
  Qed. 

  Lemma S_List_Bound n L:
    NoDup L -> (forall x, In x L -> S x /\ x <= 2 * n) 
      -> length L <= n.
  Proof.
    intros ND [LC H] % DomC_pullback_list; intuition.
    rewrite <- H.
    assert (incl LC (seq 0 n)).
    - intros c [_ [_ H3]] % H2. apply in_seq. lia.
    - apply pigeonhole_length in H1.
      + now rewrite seq_length in H1.
      + exact D_nat.
      + exact H0.
  Qed.  

  (* Listing of predicates up to a bound b *)

  Definition PredListTo p : list nat -> nat -> Prop
    := fun L b => forall x, In x L <-> p x /\ x <= b.

  Lemma PredListTo_spec {p L b}:
    PredListTo p L b -> forall x, In x L -> p x /\ x <= b.
  Proof.
    intros H x I % H.
    apply I.
  Qed.

  Lemma PredListTo_Bound {p L b}:
    PredListTo p L b -> forall x, In x L -> x <= b.
  Proof.
    intros H x I % H.
    apply I.
  Qed.

  Lemma NoDupBoundH {L} b:
    NoDup L -> (forall x, In x L -> x <= b) -> forall x, x > b -> NoDup (x::L).
  Proof.
    intros ND H x E.
    constructor.
    - intros H1 % H. lia.
    - exact ND.
  Qed. 

  Lemma PredNoDupListTo_NNExist p:
    forall b, ~~ exists L, PredListTo p L b /\ NoDup L.
  Proof.
    induction b; intros H.
    - FalseDec (p 0); apply H.
      + exists [0]. split; try split.
        * intros [E | E]; (try contradiction E).
          rewrite <- E. intuition.
        * intros E. assert (x = 0) by lia. 
          rewrite H1. intuition.
        * constructor; intuition; constructor. 
      + exists nil. split; try split.
        * contradiction.
        * intros E. assert (x = 0) by lia. 
          rewrite H1 in E. firstorder.
        * constructor.
    - apply IHb. intros [L H1].
      FalseDec (p (1 + b)); apply H.
      + exists ((1+ b) :: L). split; try split.
        * intros [E | E]; try (rewrite <- E; intuition). 
          apply H1 in E. intuition.
        * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia. 
          ** right. apply H1. intuition.
          ** left. lia.
        * apply (NoDupBoundH b). 
          ** apply H1.
          ** intros x H3 % H1. lia.
          ** lia.
      + exists L. split; try split.
        * intros E % H1. intuition.
        * intros [E1 E2]. assert (x <= b \/ x = 1 + b) as [E | E] by lia. 
          ** apply H1. intuition.
          ** rewrite E in E1. firstorder.
        * apply H1. 
  Qed. 

  Lemma complToBound_compl p L b:
    PredListTo p L b -> PredListTo (compl p) (complToBound L b) b.
  Proof.
    intros H x. split. 
    - intros H1 % list_minus_spec. 
      enough (x <= b). 
      + intuition. intros npx. apply H3, H. intuition.
      + destruct H1 as [H1 _]. apply in_seq in H1. lia.   
    - intros [H1 H2]. apply list_minus_spec. split.   
      + apply in_seq; lia.
      + intros H3 % H. firstorder.
  Qed.

  (* Length of listings of S up to 2*n is bounded by n *)

  Lemma S_Listing:
    forall n, ~~ exists L, NoDup L /\ length L <= n /\ PredListTo S L (2*n).
  Proof.
    intros n H. apply (PredNoDupListTo_NNExist S (2*n)). 
    intros [L H1]. apply H. exists L; intuition.
    apply S_List_Bound. 
    - exact H2. 
    - apply H0. 
  Qed. 

  (* Weak Existence Infinite Criterion *)

  Lemma ComplS_Listing:
  forall (n: nat) ,~~ exists L, length L >= n /\ NoDup L  
                                /\ forall x, In x L -> ~ S x.
  Proof.
    intros n H.
    apply (S_Listing n). intros [L H1]. 
    apply H. exists (complToBound L (2*n)). repeat split.
    - remember (complToBound_length L (2*n)). lia. 
    - apply complToBound_NoDup.
    - intros x I % (complToBound_compl S); intuition.
  Qed. 


  Lemma S_coInfinite:
    infinite (compl S).
  Proof.
    apply notfinite_iff3, ComplS_Listing. exact D_nat.
  Qed.

  (* S is a simple predicate *)

  Corollary S_simple:
    simple S.
  Proof.
    split.
    - exact S_SemiDec.
    - split. 
      + exact S_coInfinite.
      + exact S_No_S_Inf_Subset. 
  Qed.

End Simple_Predicate_S.


(* Prooving simple predicates to be not m-complete *)

Section Simple_Not_M_Complete.  

  (* Assuming enumerator of semidecidable predicates W, its semidecidability, 
     Variation of the SMN-Theorem, and the computability of List indices *)

  Variable W : nat -> nat -> Prop. 
  Variable es : ES W.

  Variable W_semidec: W_SEMIDEC W.

  Variable smn: (S_M_N' W).

  Variable list_id: (LIST_ID W).


  (* Productive and Creative Predicates *)

  Implicit Types (p q: nat -> Prop) (f: nat -> nat).

  Definition prod_fct p : (nat -> nat) -> Prop 
    := fun g => forall c, (W c) << p -> (p \ (W c)) (g c).

  Definition productive : (nat -> Prop) -> Prop
    := fun p => exists g, prod_fct p g.

  Lemma prod_not_semidec p:
    productive p -> ~ semidec p.
  Proof.
    intros [g P] S.
    assert (exists c, forall x, W c x <-> p x) as [c H] by apply (es p), S.
    specialize (P c).
    assert (W c << p) as Su.
    - intros x Wnx. apply H, Wnx.  
    - apply (P Su). 
      apply H, P, Su.
  Qed.
   
  Lemma manyone_productive p q:
    p <=m q -> productive p -> productive q.
  Proof.
    intros [f R] [g P].
    destruct (smn f) as [k H].
    exists (fun c => f(g(k c))).
    intros c S.  
    assert (W (k c) << p) as Su.
    - intros x Wx.
      specialize (S (f x)).
      apply (R x), S, (H c x), Wx.
    - split.
      + apply (R (g (k c))), (P (k c)), Su. 
      + intros H1. 
        apply (P (k c) Su).
        apply (H c (g (k c))), H1.
  Qed.
        
  Definition creative : (nat -> Prop) -> Prop
    := fun p => semidec p /\ productive (compl p).

  Lemma creativeW0: creative (W0 W).
  Proof.
    split.
    - now apply W0_semidec.
    - exists (fun n => n).
      intros n H. specialize (H n); firstorder.
  Qed.

  Corollary crea_not_dec p:
    creative p -> ~ decidable p.
  Proof.
    intros [S Pr] De.
    apply prod_not_semidec in Pr.
    apply Pr.  
    apply semidec_dec, decidable_closure_compl, De.
  Qed.

  Corollary manyone_creative p q:
    p <=m q -> creative p -> productive (compl q).
  Proof.
    intros R %  many_one_red_compl [T P].  
    apply (manyone_productive (compl p) (compl q) R).
    exact P.
  Qed.

  (* Complete predicates are creative *)

  Corollary complete_creative p:
    m_complete p -> creative p.
  Proof.
    intros [S C].
    split.
    - exact S.
    - apply (manyone_creative (W0 W) p).
      + apply C, W0_semidec. apply type_iso_refl.
        * exact D_nat.
        * assumption.
      + exact creativeW0.
  Qed.

  Fixpoint g_rec (g: nat -> nat) (c: nat): list nat
    := match c with 0 => []
                | Datatypes.S c => let l := g_rec g c
                        in g(proj1_sig (list_id l)) :: l  end.

  Lemma g_subset p g:
    prod_fct p g -> forall c x, In x (g_rec g c) -> p x.
  Proof.
    intros P c.
    induction c.
    - firstorder. 
    - intros x [H | H].
      + rewrite <- H.
        apply P. 
        intros x0 Wn. apply IHc.
        apply (proj2_sig (list_id (g_rec g c))) , Wn.
      + apply IHc, H.
  Qed.

  Lemma g_ind_injective p g c:
    prod_fct p g -> ~ In (g (proj1_sig (list_id (g_rec g c)))) (g_rec g c).
  Proof.
    intros P.
    intros H % (proj2_sig (list_id (g_rec g c))).  
    assert (W (proj1_sig (list_id (g_rec g c))) << p).
    - intros x Wx % (proj2_sig (list_id (g_rec g c))). 
      apply (g_subset p g P c), Wx.
    - specialize (P (proj1_sig (list_id (g_rec g c)))). 
      apply P in H0.
      destruct H0 as [_ H0].
      firstorder.
  Qed.

  Lemma g_ind_spec1 p g:
    prod_fct p g -> forall c, NoDup (g_rec g c).
  Proof.
    induction c; cbn.
    - constructor. 
    - constructor. 
      + apply (g_ind_injective p), H.
      + exact IHc.
  Qed.

  Lemma g_ind_spec2 p g:
    forall c, length (g_rec g c) = c.
  Proof.
    induction c; cbn.
    - trivial.
    - rewrite IHc. trivial.
  Qed.

  Lemma g_infinite p g:
    prod_fct p g -> infinite (fun x => exists c, In x (g_rec g c)).
  Proof.
    intros P.
    apply (of_any_number_notfinite); try exact D_nat.
    intros c. 
    exists (g_rec g c).
    split.
    - apply g_ind_spec2, p.
    - split.
      + apply (g_ind_spec1 p), P.
      + intros x H. exists c. exact H.
  Qed.

  (* Productive Predicates contain a semidecidable, infinite subset *)
   
  Theorem prod_inf_sub p:
    productive p -> exists (q: nat -> Prop), (q << p) /\ infinite q /\ semidec q.
  Proof.
    intros [g P].
    exists (fun x => exists c, In x (g_rec g c)). split.
    - intros x [c H]. apply (g_subset p g P c x), H.
    - split.
      + exact (g_infinite p g P).
      + exists (fun x c => if (dec_membership D_nat (g_rec g c) x ) then true else false).
      intros x. split; 
      intros [c H]; exists c; 
      destruct (dec_membership D_nat (g_rec g c) x ); firstorder; discriminate.
  Qed.


  (* Simple Predicates are not creative and therefore not m-complete *)

  Lemma simple_not_creative (p: nat -> Prop) :
    simple p -> ~ creative p.
  Proof.
    intros [H1 [H2 H3]] [R Pr].
    apply prod_inf_sub in Pr.
    destruct Pr as [q [Hq1 [Hq2 Hq3]]].
    specialize (H3 q Hq2 Hq3).
    exact (H3 Hq1).
  Qed.

  Lemma simple_not_complete (p: nat -> Prop) :
    simple p -> ~ m_complete p.
  Proof.
    intros S C % complete_creative.
    exact (simple_not_creative p S C).
  Qed.

End Simple_Not_M_Complete.


(* Construction and Verification of S* *)

Section S_Star. 
  Import  Coq.Init.Nat. 

  (* Assuming enumerator of semidecidable predicates W, its semidecidability, 
     Variation of the SMN-Theorem, and the computability of List indices *)

  Variable W : nat -> nat -> Prop. 
  Variable es : ES W.

  Variable W_SDec: nat * nat -> nat -> bool.
  Variable W_semidecider: semidecider (fun '(c,x) => W c x) W_SDec.

  Variable c_top : nat.
  Variable c_top_spec: forall x, W c_top x.

  Definition S' : nat -> Prop 
    := S W W_SDec W_semidecider c_top c_top_spec.

  (* Auxiliary List *)

  Definition S_Pow n : list nat 
    := seq (2^n - 1) (2^n).

  Lemma pow_pos n:
    2^n > n.
  Proof.
    induction n; cbn; lia.
  Qed.

  Lemma pow_sum n:
    2 ^ n - 1 + 2 ^ n = 2 ^ (1 + n) - 1.
  Proof.
    induction n; cbn in *; lia.
  Qed.

  Lemma S_Pow_injective x n1 n2:
    In x (S_Pow n1) /\ In x (S_Pow n2) -> n1 = n2.
  Proof.
    intros [H1 H2]. 
    apply in_seq in H1. apply in_seq in H2. 
    assert (n1 = n2 \/ 1 + n1 <= n2 \/ 1 + n2 <= n1) by lia.
    destruct H as [H | [H | H]].
    - exact H.
    - assert (2 ^ (1 + n1) - 1 <= x).
      + enough (2 ^ (1 + n1) <= 2 ^ n2) by lia.
        apply Nat.pow_le_mono_r; lia. 
      + assert (2 ^ n1 - 1 + 2 ^ n1 = 2 ^ (1 + n1) - 1) by apply pow_sum.
        lia.
    - assert (2 ^ (1 + n2) - 1 <= x).
      + enough (2 ^ (1 + n2) <= 2 ^ n1) by lia.
        apply Nat.pow_le_mono_r; lia. 
      + assert (2 ^ n2 - 1 + 2 ^ n2 = 2 ^ (1 + n2) - 1) by apply pow_sum.
        lia.
  Qed.

  (* Definition S* *)

  Definition S_Star : nat -> Prop
    := fun x => S' x 
                  \/ exists n, (fun '(c,x0) => W c x0) (nat_to_nat2 n) 
                                /\ In x (S_Pow n).

  Definition S_Star_compl : nat -> Prop 
    := fun x => (compl S') x /\ ~ exists n, ((fun '(c,x0) => W c x0) (nat_to_nat2 n) 
                                              /\ In x (S_Pow n )).

  Lemma S_Star_comp_agree:
    forall x, (compl S_Star) x <-> S_Star_compl x.
  Proof. 
    intros x. unfold S_Star_compl,  S_Star, compl, not. now rewrite Decidable.not_or_iff.  
  Qed.


  (* S* is semidecidable *)

  Lemma S_Star_semidec:
    semidec S_Star.
  Proof.   
    apply semidec_closure_disj.
    - apply S_SemiDec.
    - apply semidec_closure_ex.
      apply semidec_closure_conj.
      + exists (fun pa n => W_SDec (nat_to_nat2 (fst pa)) n). 
        intros [n0 x0]; specialize (W_semidecider (nat_to_nat2 n0)); firstorder.
      + apply semidec_dec. apply decidable_agreement. constructor. 
        intros pa. apply (dec_membership D_nat).
  Qed.


  (* Complement of S* contains no semidecidable, infinite subset *)

  Lemma S_Star_No_S_Inf_Subset:
    forall (q: nat -> Prop), infinite q -> semidec q -> ~ (q << (compl (S_Star))).
  Proof.
    intros q H1 H2 H3.
    eapply (S_No_S_Inf_Subset W es).
    - exact H1.
    - exact H2.
    - intros x qx % H3.  
      intros nSx. apply qx. left. exact nSx. 
  Qed. 


  (* Co-Infinite Proof of S* *)

  Lemma W_CoInfinite:
    infinite (compl (fun '(c,x) => W c x)).
  Proof.   
    destruct (W_empty W es) as [c_bot H].
    apply (inf_closure_inj_notfinite (Top nat)). exact D_nat. exact D_nat2.
    - exists (fun n => (c_bot, n)).
      intros n1 n2; firstorder. now inversion H2.
    - exact N_infinite_notfinite. 
  Qed.

  Lemma WNat_CoInfinite:
    infinite (compl (fun n => (fun '(c,x) => W c x) (nat_to_nat2 n))).
  Proof.   
    apply (inf_closure_surj_notfinite (compl (fun n => (fun '(c,x) => W c x) (nat_to_nat2 n))) (compl (fun '(c,x) => W c x))).
    - exists nat_to_nat2.
      intros p H. exists (nat2_to_nat p). unfold compl.
      rewrite nat_to_nat2_nat2_to_nat_cancel; firstorder.
    - exact W_CoInfinite. 
  Qed.

  Lemma S_Pow_NotInS n:
    ~ Forall S' (S_Pow n). 
  Proof.
    intros H.
    assert (length (S_Pow n) <= 2^n - 1).
    - eapply S_List_Bound. 
      + apply seq_NoDup. 
      + intros x. split. 
        * revert H0. apply Forall_forall. exact H.
        * apply in_seq in H0. lia. 
    - unfold S_Pow in H0. rewrite seq_length in H0. clear H. 
      induction n; cbn in H0; lia.
  Qed.

  Lemma Not_Forall_2_WeakEx {X} (p: X -> Prop) L:
    (~ Forall p L) -> ~~ exists x, In x L /\ ~ p x.
  Proof.
    intros H1 H2.
    induction L. 
    - now apply H1.
    - FalseDec (p a). 
      + apply IHL. 
        * contradict H1. now constructor.
        * contradict H2. destruct H2. exists x; firstorder.
      + apply H2. exists a. firstorder.
  Qed. 
   
  Lemma S_Pow_WeakEx_NotS n:
    ~~ exists x, In x (S_Pow n) /\ (compl S') x.
  Proof.
    apply Not_Forall_2_WeakEx, S_Pow_NotInS.
  Qed.

  Lemma S_Star_coInfinite:
    infinite (compl S_Star).
  Proof.
    apply notfinite_iff4. 
    intros n0. 
    assert (~ ~ (exists n : nat, n >= n0 + 1/\ compl (fun n : nat => let '(c, x) := nat_to_nat2 n in W c x) n)).
    - apply notfinite_iff4, WNat_CoInfinite. 
    - contradict H. intros [n H2].
      apply (S_Pow_WeakEx_NotS n). 
      intros [x [H3 H4]]. apply H.  
      exists x; split. 
      + apply in_seq in H3. enough (2 ^ n > n) by lia. apply pow_pos.
      + apply S_Star_comp_agree. 
        unfold S_Star_compl. split.
        * exact H4.
        * intros [n1 [H5 H6]].
          assert (n = n1) by now apply (S_Pow_injective x). 
          apply H2. now rewrite H0.
  Qed.


  (* S* is simple *)

  Corollary S_Star_simple:
    simple S_Star.
  Proof.
    split.
    - exact S_Star_semidec.
    - split.
      + exact S_Star_coInfinite.
      + exact S_Star_No_S_Inf_Subset.
  Qed.


  (* W truth-table reduces to S* *) 

  Lemma S_Star_split L:
    Forall S_Star L 
      -> Forall S' L \/ exists n, (fun '(c,x) => W c x) (nat_to_nat2 n) /\ exists x, In x L /\ In x (S_Pow n).
  Proof.
    induction 1.
    - left; constructor.
    - destruct IHForall.
      + destruct H. 
        * left; now constructor.
        * right. destruct H. 
          exists x0. intuition. 
          exists x; intuition.
      + right. destruct H1. 
        exists x0. intuition. destruct H3.   
        exists x1; intuition.
  Qed.

  Lemma tt_red_W_S_Star:
    (fun '(c,x) => W c x) <=tt S_Star. 
  Proof.
    exists (fun '(c, x) => let n := nat2_to_nat (c,x) in S_Pow n). 
    assert (forall b, {b = true} + {~ (b = true)}) by (intros [|]; firstorder; exact (0,0)). 
    exists (fun _ L _ => if (Forall_dec (fun b => b = true) H L) then true else false).
    intros [c x] L.
    destruct (Forall_dec (fun b => b = true) H L).
    - intros H1; intuition.
      apply corresponding_all_true in H0; intuition.
      apply S_Star_split in H0 as [H0 | H0]. 
      + apply S_Pow_NotInS in H0. contradict H0. 
      + destruct H0 as [n [H0 [x0 H3]]]. 
        apply S_Pow_injective in H3.
        now rewrite <- H3, nat_to_nat2_nat2_to_nat_cancel in H0.
    - split; intros. 
        + contradict n. 
          assert (Forall S_Star (S_Pow (nat2_to_nat (c,x)))). 
          * apply Forall_forall.
            intros x0 H3. right. 
            exists (nat2_to_nat (c, x)).
            rewrite nat_to_nat2_nat2_to_nat_cancel; intuition.    
          * apply corresponding_all_p in H1; intuition. 
        + discriminate. 
  Qed.  
End S_Star.

