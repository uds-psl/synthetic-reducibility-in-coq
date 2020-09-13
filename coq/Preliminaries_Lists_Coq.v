Require Export List.

From Coq Require Import Arith Lia.

Require Import Preliminaries_Coq.

(* Preliminary Definitions and Results regarding Lists *)

Section MyList. 

  (* Injective Mappings *)

  Lemma map_setinj_elem {X Y} (f: X -> Y) p q L:
    set_injection p q f -> (forall x, In x L -> p x) -> 
      forall x, p x -> In x L <-> In (f x) (map f L).
  Proof.
    intros Inj P x px.
    rewrite in_map_iff. split. 
    - intros H. eauto. 
    - intros [x0 [E H1]]. 
      assert (x = x0). 
      + apply Inj; intuition.
      + rewrite H. exact H1.
  Qed. 

  Lemma map_setinj_NoDup {X Y} (f: X -> Y) p q L:
    set_injection p q f -> (forall x, In x L -> p x) -> 
      NoDup L <-> NoDup (map f L).
  Proof.
    intros Inj P.
    induction L; cbn.
    - split; constructor. 
    - rewrite NoDup_cons_iff, NoDup_cons_iff. 
      rewrite IHL, (map_setinj_elem f p q L Inj).
      + firstorder.
      + intros x H. apply P. intuition.
      + apply P. intuition.
      + intros x H. apply P. intuition.  
  Qed.

  Corollary map_inj_elem {X Y} (f: X -> Y) L:
    injective f ->  forall x, In x L <-> In (f x) (map f L).
  Proof.
    intros H1 x.
    apply (map_setinj_elem f (Top X) (Top Y)); firstorder.
  Qed.

  Corollary map_inj_NoDup {X Y} (f: X -> Y) L:
    injective f -> NoDup L <-> NoDup (map f L).
  Proof.
    intros H1.
    apply (map_setinj_NoDup f (Top X) (Top Y)); firstorder. 
  Qed.     


  (* Maximum Function *)

  Fixpoint list_max L : nat
    := match L with nil => 0 | 
                 (a::L) => let m := list_max L in
                           if le_gt_dec a m then m else a end.

  Lemma list_max_not_in L:
    forall x, x > list_max L -> ~ In x L.
  Proof.
    intros x.
    induction L.
    - intros _. firstorder.
    -  intros H1. cbn in *; destruct (le_gt_dec a (list_max L)); cbn in *. 
      + intros [H2 | H2].
        * rewrite <- H2 in H1. lia.
        * apply IHL in H1. firstorder.
      + intros [H2 | H2].
        * rewrite H2 in H1. lia.
        * apply IHL. lia. exact H2.
  Qed.

  Lemma list_max_in (L: list nat):
    forall x, In x L -> x <= list_max L.
  Proof.
    intros x H. 
    destruct (Nat.le_gt_cases x (list_max L)); intuition.
    apply list_max_not_in in H0. firstorder.
  Qed.


  (* Removing Function for General Predicates *)

  Context {LX: Type}.

  Fixpoint remove_pred (p: LX -> Prop) (D: dec_pred p) L : list LX 
    := match L with nil => nil |
                 (a::L) => if D a then remove_pred p D L else a :: (remove_pred p D L) end.

  Lemma remove_pred_spec1 p D L:
    forall x, In x L -> (~ p x) -> In x (remove_pred p D L).
  Proof.
    intros x H1 H2. induction L.
    - firstorder.
    - destruct H1.
      + rewrite H. cbn; destruct D.
        * firstorder.
        * now left.
      + apply IHL in H. cbn; destruct D; firstorder.
  Qed.

  Lemma remove_pred_spec2 p D L:
    forall x, In x (remove_pred p D L) -> In x L /\ (~ p x).
  Proof.
    intros x H. induction L; cbn in H.
    - firstorder.
    - destruct D.
      + apply IHL in H. firstorder.
      + destruct H.
        * rewrite <- H. firstorder.
        * apply IHL in H. firstorder.
  Qed. 


  (* Membership Decider & Removing of an Element *)

  Variable D : discrete LX.

  Lemma dec_membership:
    forall (L: list LX), @dec_pred LX (fun x => In x L).
  Proof.
    intros L x. 
    induction L.
    - right. firstorder.
    - destruct IHL, (D (x,a)); firstorder; tauto.
  Qed.

  Definition remove x L : list LX
    := remove_pred (fun a => x = a) (fun a => D(x,a)) L.

  Lemma remove_spec1 x L:
    length (remove x L) <= length L.
  Proof.
    induction L.
    - firstorder.
    - cbn; destruct (D (x,a)); unfold remove in IHL.
      + lia.
      + cbn. lia.
  Qed.

  Lemma remove_spec2 x L:
    In x L -> length (remove x L) < length L.
  Proof.
    intros H. 
    induction L.
    - firstorder.
    - assert (length (remove x L) <= length L) by (exact (remove_spec1 x L)).
      destruct H, (D (x,a)) eqn: H1; cbn; rewrite H1.
      + unfold remove in H0. lia.
      + assert (x = a) by (rewrite H; trivial). 
        exfalso. firstorder.
      + unfold remove in IHL. apply IHL in H. lia.
      + assert (length (remove x L) < length L) by (exact (IHL H)). 
        unfold remove in H2. cbn. lia.
  Qed.
        
  Lemma remove_spec3 x x0 L:
      In x0 L -> (~ In x0 (remove x L)) -> x = x0.
  Proof.
    intros H H1. destruct (D (x,x0)); try assumption.
    contradict H1. now apply remove_pred_spec1.
  Qed. 

  Lemma remove_spec4 x x0 L:
     In x0 (remove x L) -> In x0 L.
  Proof.
    now intros H % remove_pred_spec2.
  Qed.

  Lemma remove_NoDup x L:
    NoDup L -> NoDup (remove x L).
  Proof.
    intros ND. induction ND.
    - constructor.
    - cbn. destruct (D (x,x0)).
      + exact IHND.
      + constructor.
        * intros H1 % remove_spec4. apply H, H1.
        * exact IHND.
  Qed.


  (* Pigeonhole Principles *)

  Lemma pigeonhole_exists (L1: list LX):
     NoDup L1 -> forall L2, length L1 > length L2 -> exists x, In x L1 /\ ~ In x L2.
  Proof.
    intros H. induction L1. 
    - intros L2 E. cbn in E. lia.
    - intros L2 E. 
      apply NoDup_cons_iff in H.
      destruct (dec_membership L2 a). 
      + specialize (IHL1 (proj2 H) (remove a L2)). 
        assert (length (remove a L2) < length L2) by (apply remove_spec2, i).
        assert (length L1 > length (remove a L2)) by (cbn in E; lia).
        destruct (IHL1 H1) as [x0 [H31 H32]].
        exists x0. split.
          * right. exact H31.
          * intros e % (remove_spec3 a x0 L2).
            ** rewrite e in H. firstorder.
            ** exact H32.
      + exists a. firstorder.
  Qed.

  Lemma pigeonhole_length (L1: list LX):
     NoDup L1 -> forall L2, incl L1 L2 -> length L1 <= length L2. 
  Proof.
    intros H L2 H1.
    destruct (Nat.le_gt_cases (length L1) (length L2)).
    - assumption.
    - apply pigeonhole_exists in H0.
      + destruct H0 as (x & H2 & H3). firstorder.
      + assumption.
  Qed.


  (* Difference Function of Lists *)
  Fixpoint list_minus (L1 L2: list LX) : list LX
    := match L1 with nil => nil |
               (x :: L1) => let L := list_minus L1 L2 in 
                            if dec_membership L2 x then L else x :: L end.

  Lemma list_minus_spec L1 L2:
    forall x, In x (list_minus L1 L2) <-> In x L1 /\ ~ In x L2.
  Proof.
    intros x. induction L1.
    - cbn. firstorder.
    - cbn. destruct (dec_membership L2 a); split.
      + intuition.
      + intros [[<- | H0] H1]. 
        * intuition.
        * apply IHL1; intuition.
      + intros [<- | H0 % IHL1]; intuition.
      + intros [[<- | H0] H1].
        * intuition.
        * right. apply IHL1; intuition.
  Qed.

  Lemma list_minus_NoDup L1 L2:
    NoDup L1 -> NoDup (list_minus L1 L2).
  Proof.
    intros ND.
    induction ND.
    - cbn. constructor.
    - destruct (dec_membership L2 x) eqn: E; cbn; rewrite E.
      + exact IHND.
      + constructor.
        * intros H1 % list_minus_spec. firstorder.
        * exact IHND. 
  Qed.

  Lemma list_minus_remove L1 L2 a:
      ~ In a L1 -> incl (list_minus L1 (remove a L2)) (list_minus L1 L2).
  Proof.
    intros H1 x H2 % list_minus_spec. apply list_minus_spec. split.
    - apply H2. 
    - intros H3. assert (a = x). apply (remove_spec3 a x L2); intuition.
      rewrite <- H in H2. firstorder.
  Qed.

  Lemma list_minus_length L1 L2:
    NoDup L1 -> length (list_minus L1 L2) + length L2 >= length L1.
  Proof.
    intros ND.  
    revert L2.
    induction ND.
    - cbn. lia.
    - intros L2. destruct (dec_membership L2 x) eqn: E; cbn; rewrite E.  
      + specialize (IHND (remove x L2)). remember (remove_spec2 x L2 i).
        enough (length (list_minus l L2) >= length (list_minus l (remove x L2))) by lia.
        apply NoDup_incl_length. 
        * apply list_minus_NoDup, ND.
        * apply list_minus_remove, H.
      + cbn. specialize (IHND L2). lia.
  Qed. 


  (* Facts about firstn (Defined in Standard Library) *)

  Lemma firstn_elements L n:
    forall x, In x (firstn n L) -> @In LX x L.
  Proof.
    intros x H.
    rewrite <- (firstn_skipn n L).
    apply in_or_app; firstorder.
  Qed.

  Lemma firstn_NoDup L n:
    NoDup L -> @NoDup LX (firstn n L).
  Proof.
    intros H. revert n.
    induction H.
    - intros n. rewrite firstn_nil. constructor.
    - destruct n ; cbn; constructor.  
      + intros H1 % firstn_elements. firstorder. 
      + apply IHNoDup. 
  Qed.

End MyList.


(* Lists of Pairs, Projections *)

Section PairList.

  Context {LX LY: Type}.

  Definition fstL (L: list (LX * LY)) : list LX 
    := map fst L.

  Definition sndL (L: list (LX * LY)) : list LY
    := map snd L.

  Lemma fstL_in x L:
    In x (fstL L) <-> exists y, In (x,y) L.
  Proof.
    unfold fstL. rewrite in_map_iff. firstorder. 
    exists (snd x0).
    rewrite <- H, <- (surjective_pairing x0). 
    exact H0.
  Qed.

  Lemma sndL_in y L:
    In y (sndL L) <-> exists x, In (x,y) L.
  Proof.
    unfold sndL. rewrite in_map_iff. firstorder. 
    exists (fst x).
    rewrite <- H, <- (surjective_pairing x). 
    exact H0.
  Qed.

  Lemma fstL_length L:
    length L = length (fstL L).
  Proof.
    unfold fstL. rewrite map_length. trivial.
  Qed. 

  Lemma sndL_length L:
    length L = length (sndL L).
  Proof.
    unfold sndL. rewrite map_length. trivial.
  Qed.

  Variable DX: discrete LX.

  Variable DY: discrete LY.

  Definition in_fst L : forall x, {In x (fstL L)} + {~ In x (fstL L)}
    := dec_membership DX (fstL L).

  Definition in_snd L : forall y, {In y (sndL L)} + {~ In y (sndL L)}
    := dec_membership DY (sndL L).

End PairList.


(* Function computing the complement of a list up to a bound *)

Section ComplToBound.

  Definition complToBound L b : list nat 
    := list_minus D_nat (seq 0 (S b)) L.

  Lemma complToBound_Bound L b :
    forall x, In x (complToBound L b) -> x <= b.
  Proof.
    intros x [H _] % list_minus_spec.
    apply in_seq in H. lia.
  Qed.

  Lemma complToBound_length L b:
    length (complToBound L b) + length L >= S b.
   
  Proof.
    assert (length (seq 0 (S b) ) = S b) by exact (seq_length (S b) 0). rewrite <- H.
    apply list_minus_length.
    apply seq_NoDup.
  Qed.
    
  Lemma complToBound_NoDup L b:
    NoDup (complToBound L b).
  Proof.
    apply list_minus_NoDup. apply seq_NoDup. 
  Qed.

End ComplToBound. 
