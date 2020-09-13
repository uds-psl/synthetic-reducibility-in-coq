(* Myhill's Isomorphism Theorem *)

Require Export List.
Import ListNotations.

From Coq Require Import Arith Lia.

Require Import Preliminaries_Coq Preliminaries_Lists_Coq Definitions_Coq 
               Recursive_Mu_Operator_Coq Synthetic_Computability_Theory_Coq.

(* Correspondence Sequences *)

  Section CorSeq.

  Definition swap {X Y} (L: list (X * Y)) : list (Y * X)
    := map (fun '(x,y) => (y,x)) L.

  Lemma swap_equal1 {X Y} (L: list (X * Y)):
    (fstL L) = (sndL (swap L)).
  Proof.
    induction L.
    - trivial.
    - destruct a. cbn. unfold fstL in IHL. rewrite IHL. trivial.
  Qed.

  Lemma swap_equal2 {X Y}  (L: list (X * Y)):
    (sndL L) = (fstL (swap L)).
  Proof.
    induction L.
    - trivial.
    - destruct a. cbn. unfold sndL in IHL. rewrite  IHL. trivial.
  Qed.

  Lemma swap_in {X Y}  (L: list (X * Y)):
    forall x y, In (x,y) L <-> In (y,x) (swap L).
  Proof.
    intros x y. unfold swap. rewrite in_map_iff. split.
    - intros H. exists (x,y). intuition.
    - intros [[y0 x0] [E H]]. inversion E. rewrite <- H2. rewrite <- H1. exact H.
  Qed.

  Definition CorSeq {X Y} p q (L: list (X * Y)) : Prop 
    := NoDup (fstL L) /\ NoDup (sndL L) /\ forall x y, In (x,y) L -> p x <-> q y.

  Lemma CorSeq_swap {X Y} p q (L: list (X * Y)):
    CorSeq p q L -> CorSeq q p (swap L).
  Proof.
    intros [H3 [H4 H5]].
    split.
    - rewrite <- swap_equal2. exact H4.
    - split.
      + rewrite <- swap_equal1. exact H3.
      + intros x y H % swap_in. apply H5 in H. firstorder. 
  Qed. 

  Context {X Y: Type}.

  Lemma CorSeq_fstOneOne (L: list (X*Y)) y:
    NoDup (sndL L) -> forall x1 x2, In (x1,y) L -> In (x2,y) L -> x1 = x2.
  Proof.
    intros ND2. induction L.
    - firstorder.
    - destruct a as [ax ay]. 
      intros x1 x2 [H1 | H1] [H2 | H2].
      + inversion H1. inversion H2. now rewrite <- H0, H4. 
      + inversion H1. rewrite <- H3 in H2.
        inversion ND2. contradict H5. 
        apply sndL_in. exists x2. exact H2.
      + inversion H2. rewrite <- H3 in H1. 
        inversion ND2. contradict H5. 
        apply sndL_in. exists x1. exact H1.
      + inversion ND2. apply (IHL H4 x1 x2 H1). exact H2.
  Qed.

  Lemma CorSeq_sndOneOne (L: list (X*Y)) x:
    NoDup (fstL L) -> forall y1 y2, In (x,y1) L -> In (x,y2) L -> y1 = y2.
  Proof.
    intros ND1. induction L.
    - firstorder.
    - destruct a as [ax ay]. intros y1 y2 [H1 | H1] [H2 | H2].
      + inversion H1. inversion H2. now rewrite <- H3, H5. 
      + inversion H1. rewrite <- H0 in H2.
        inversion ND1. contradict H5. 
        apply fstL_in. exists y2. exact H2.
      + inversion H2. rewrite <- H0 in H1. 
        inversion ND1. contradict H5. 
        apply fstL_in. exists y1. exact H1.
      + inversion ND1. apply (IHL H4 y1 y2 H1). exact H2.
  Qed.     

  Variable DX: discrete X.
  Variable DY: discrete Y.


  (* Finding a corresponding element in a list *)

  Fixpoint find_X y L : option X
    := match L with nil => None |
               (x,y1)::L => if DY (y,y1) then Some x else find_X y L end. 

  Lemma find_X_spec1 y L:
    In y (sndL L) <-> exists x, find_X y L=  Some x.
  Proof.
    induction L; unfold find_X.
    - firstorder; discriminate.
    - destruct a. fold find_X. destruct (DY (y, y0)).
      + rewrite e. split; intros _.
        * eauto. 
        * apply sndL_in. exists x. intuition.
      + split.
        * intros [H | H]. 
          ** cbn in H. contradict n. now firstorder.
          ** apply IHL, H.
        * intros H % IHL. right. exact H.
  Qed. 

  Corollary find_X_spec2 x y L:
    find_X y L = Some x -> In (x,y) L.
  Proof.
    induction L.
    - cbn. discriminate.
    - destruct a as [x2 y2]. unfold find_X. fold find_X. destruct (DY (y, y2)).
      + intros H. inversion H. rewrite e. intuition.
      + intuition.
  Qed.

  (* Trace Function traveling through a list for given steps *)

  Fixpoint trace f L x n : list X
    := match n with 0 => if find_X (f x) L then [x] else nil |
                  S n => match find_X (f x) L with None => [] |
                                          Some x1 => x :: (trace f L x1 n) end end.

  Lemma trace_NoDup_help f L x n:
    forall x1, In x1  (trace f L x n) 
      -> x1 = x \/ exists y1, In y1 (map f (trace f L x n)) /\ In (x1,y1) L.
  Proof.
    revert x. induction n; cbn. 
    - intros x x1. destruct find_X; firstorder. 
    - intros x x1. cbn. destruct find_X as [x2|] eqn: IY; cbn.
      + intros [H | H]. 
        * intuition.  
        * specialize (IHn x2 x1 H) as [IHn | IHn].
          ** right. exists (f x). intuition. 
             rewrite IHn. apply (find_X_spec2 x2 (f x)), IY.
          ** right. destruct IHn. exists x0. intuition.
      + firstorder.
  Qed.

  Lemma trace_NoDup_strong {p q} f L x n:
    one_one_redfunc p q f -> CorSeq p q L -> ( forall y, In (x, y) L -> ~ In y (map f (trace f L x n))) 
      -> NoDup (trace f L x n).
  Proof.
    intros [I _] [ND1 _].
    revert x. 
    induction n; cbn. 
    - intros x _. destruct find_X; constructor; firstorder; constructor.
    - intros x H. destruct find_X as [x1|] eqn: IY.
      + assert (~ In x (trace f L x1 n)).
        * intros [H1 | H1] % trace_NoDup_help.
          ** rewrite <- H1 in IY. apply find_X_spec2 in IY. apply (H (f x) IY). 
             apply in_map_iff. exists x. intuition.
          ** destruct H1 as [y2 [H2 H3]]. apply (H y2 H3). now right. 
        * cbn ; constructor.
          ** exact H0.
          ** apply IHn. intros y H1. assert (y = f x). 
             apply find_X_spec2 in IY. 
             apply (CorSeq_sndOneOne L x1) ; intuition.  
             rewrite H2. rewrite <- map_inj_elem; intuition. 
      + clear. constructor; firstorder; constructor.
  Qed.

  Lemma trace_NoDup {p q} f L x n:
    one_one_redfunc p q f -> CorSeq p q L -> (~ In x (fstL L)) 
      -> NoDup (trace f L x n).
  Proof.
    intros R C H. 
    apply (trace_NoDup_strong f L x n R C). 
    intros y H1. contradict H. 
    apply fstL_in. exists y; exact H1. 
  Qed.

  Lemma map_trace_incl f L x n:
    incl (map f (trace f L x n)) (sndL L).
  Proof.
    intros x'. revert x. induction n; cbn; intros x; destruct find_X eqn: I. 
    - intros H. inversion H; firstorder. 
      apply find_X_spec2 in I. apply sndL_in. 
      exists x0. now rewrite <- H.
    - firstorder. 
    - intros [H | H]. 
      + apply find_X_spec2 in I. apply sndL_in. 
        exists x0. now rewrite <- H.
      + apply (IHn x0), H.
    - firstorder. 
  Qed.

  Lemma trace_element {p q} f L x n: 
     one_one_redfunc p q f -> CorSeq p q L 
        -> {y | (p x <-> q y) /\ ~ In y (sndL L)} + {length (trace f L x n) = S n}.
  Proof.
    intros One C. revert x. induction n; intros x; cbn.
    - destruct find_X eqn: I. 
      + now right. 
      + left. exists (f x). split; try apply One. 
        intros [x' H] % find_X_spec1. now rewrite I in H. 
    - destruct find_X as [x1|] eqn: I.
      + destruct (IHn x1) as [[y [IH1 IH2]] | IH].
        * left. exists y. split. 
          ** rewrite <- IH1. apply find_X_spec2 in I. 
             apply C in I. rewrite I. apply One. 
          ** exact IH2.  
        * right. cbn. now rewrite IH. 
      + left. exists (f x). split; try apply One.
        intros [x' H] % find_X_spec1. now rewrite I in H. 
  Qed.
   
  Theorem CorSeq_Extension_help {p q} f (L: list (X * Y)) x:
    one_one_redfunc p q f -> CorSeq p q L -> (~ In x (fstL L)) ->  
      {y| (p x <-> q y) /\ ~ In y (sndL L)}.
  Proof.
    intros. destruct (trace_element f L x (length L) H H0) as [s | H2].
    - exact s. 
    - enough (length (map f (trace f L x (length L))) <= length L)  by (rewrite map_length in H3; lia).
      rewrite sndL_length. apply pigeonhole_length.
      + assumption.
      + apply map_inj_NoDup. 
        * apply H.
        * rewrite <- sndL_length.
          apply (trace_NoDup f L x (length L) H H0), H1.
      + intros y H3. eapply map_trace_incl. exact H3.
  Qed. 


  (* Computing an Extension of a Corresponding Sequence when given a one-one reduction *)

  Theorem CorSeq_Extension {p q} f (L: list (X * Y)) x: 
    one_one_redfunc p q f -> CorSeq p q L 
      -> {L' | CorSeq p q L' /\ In x (fstL L') /\ incl L L'}.
  Proof.
    intros H1 H2. 
    destruct (dec_membership DX (fstL L) x).
    - exists L. intuition.
    - destruct (CorSeq_Extension_help f L x H1 H2 n) as (y & H). 
      exists ((x, y) :: L). split. 
      + split; try split.
        * cbn; constructor; intuition. apply H2.  
        * cbn; constructor; intuition. apply H2.
        * intros x0 y0 [I | I]. 
          ** inversion I. rewrite <- H3, <- H4. apply H.  
          ** now apply H2.
      + firstorder. 
  Qed.

End CorSeq.


(* We assume p =1 q and construct an isomorphism to prove p == q *)
 
Section Myhill.

  Variable p q : nat -> Prop.
  Variable f1 f2: nat -> nat.
  Variable H1: one_one_redfunc p q f1.
  Variable H2: one_one_redfunc q p f2.


  (* Extend Corresponding Sequences in both components *)

  Theorem CorSeqBuild_sig L n:
    CorSeq p q L -> 
      {L_n | CorSeq p q L_n /\ In n (fstL L_n) /\ In n (sndL L_n) /\ incl L L_n}.
  Proof.
    intros H. 
    apply (CorSeq_Extension D_nat D_nat f1 L n) in H as (L1 & [H3 H4]); intuition.
    apply CorSeq_swap in H3. 
    apply (CorSeq_Extension D_nat D_nat f2 (swap L1) n) in H3 as  (L' & H5); intuition.
    exists (swap L'). split.
    - now apply CorSeq_swap.
    - split. 
      + rewrite <- swap_equal2. apply fstL_in in H as [y H].
        apply swap_in, H6 in H. 
        apply sndL_in. now exists y.
      + split.
        * now rewrite <- swap_equal1.
        * intros [z1 z2] I. rewrite <- swap_in. 
          apply H6. rewrite <- swap_in. now apply H0.
  Qed.      

  Definition CorSeqBuild L0 n H : list (nat * nat)
    := proj1_sig (CorSeqBuild_sig L0 n H).

  Definition CorSeqBuild_spec L0 n H 
    := proj2_sig (CorSeqBuild_sig L0 n H).

  Definition CorSeqBuild_CorSeq L0 n H : CorSeq p q (CorSeqBuild L0 n H) 
    := proj1 (CorSeqBuild_spec L0 n H).

  Definition CorSeqBuild_pair L0 n H: {L | CorSeq p q L} 
    := exist (fun L => CorSeq p q L) (CorSeqBuild L0 n H) (CorSeqBuild_CorSeq L0 n H).  


  (* Recursive Extension of Corespondence Sequences *)

  Lemma CorSeqNil:
    CorSeq p q nil.
  Proof.
    unfold CorSeq; intuition; try constructor; firstorder.
  Qed.

  Fixpoint psi_L_rec n :  {L | CorSeq p q L} 
    := match n with 0 =>  CorSeqBuild_pair nil 0 CorSeqNil | 
                  S n =>  let (L0, H) := psi_L_rec n in CorSeqBuild_pair L0 (S n) H end.

  Definition psi_L n : list (nat * nat)
    := proj1_sig (psi_L_rec n).

  Definition psi_L_CorSeq n 
    := proj2_sig (psi_L_rec n).

  Lemma psi_L_mono_help n:
    forall z, In z (psi_L n) -> In z (psi_L (S n)).
  Proof.
    unfold psi_L. unfold psi_L_rec. fold psi_L_rec. destruct psi_L_rec as [L0 H].
    set (H3 := proj2 (CorSeqBuild_spec L0 (S n) H)). cbn. apply H3.
  Qed. 
   
  Lemma psi_L_mono n:
    forall n1, n1 <= n -> forall z, In z (psi_L n1) -> In z (psi_L n).
  Proof.
    induction n.
    - intros n1 H. assert (n1 = 0) by lia. 
      rewrite H0. firstorder.
    - intros n1 E. assert (n1 <= n \/ n1 = S n) as [H | H] by lia.
      + intros z H3. apply psi_L_mono_help, (IHn n1). 
        * lia.
        * exact H3.
      + rewrite H. firstorder. 
  Qed.

  Lemma fst_psi_L_elem n:
    In n (fstL (psi_L n)).
  Proof.
    destruct n.
    - cbn. exact (proj1 (proj2 (CorSeqBuild_spec [] 0 CorSeqNil))).
    - unfold psi_L. unfold psi_L_rec. fold psi_L_rec. 
      destruct (psi_L_rec n) as [L0 H].
      exact (proj1 (proj2 (CorSeqBuild_spec L0 (S n) H))).
  Qed.

  Lemma snd_psi_L_elem n:
    In n (sndL (psi_L n)).
  Proof.
    destruct n.
    - cbn. exact (proj1 (proj2 (proj2 (CorSeqBuild_spec [] 0 CorSeqNil)))).
    - unfold psi_L. unfold psi_L_rec. fold psi_L_rec. 
      destruct (psi_L_rec n) as [L0 H].
      exact (proj1 (proj2 (proj2 (CorSeqBuild_spec L0 (S n) H)))).
  Qed.

  Lemma fstL_in_sig_nat (x: nat) (L: list (nat * nat)):
    In x (fstL L) -> {y | In (x,y) L}.
  Proof.
    apply (fstL_in_sig (fun x => x)).
    - exact D_nat2.
    - intros y. eauto.
  Qed. 


  (* Definition of the isomorphsim psi *)

  Definition psi_N : nat -> nat
    := fun n => proj1_sig (fstL_in_sig_nat n (psi_L n) (fst_psi_L_elem n)).

  (* Psi is injective, surjective, and respects p and q *)

  Lemma inj_psi:
    injective psi_N.
  Proof.
    intros x1 x2 H. unfold psi_N in H. 
    destruct (fstL_in_sig_nat x1 (psi_L x1) (fst_psi_L_elem x1)) as [y1 I1].
    destruct (fstL_in_sig_nat x2 (psi_L x2) (fst_psi_L_elem x2)) as [y2 I2].
    cbn in H. destruct (Nat.le_ge_cases x1 x2).
    - apply (psi_L_mono x2 x1 H0) in I1.
      eapply CorSeq_fstOneOne.
      + apply psi_L_CorSeq.
      + exact I1.
      + rewrite <- H in I2. exact I2.
    - apply (psi_L_mono x1 x2 H0) in I2. 
      eapply CorSeq_fstOneOne.
      + apply psi_L_CorSeq.
      + exact I1.
      + rewrite <- H in I2. exact I2.
  Qed.

  Lemma sur_psi:
    surjective psi_N.
  Proof.
    intros y. 
    set (H := snd_psi_L_elem y). apply sndL_in in H as [n H].
    exists n. unfold psi_N.
    set (H3 := proj2_sig (fstL_in_sig_nat n (psi_L n) (fst_psi_L_elem n))). cbn in H3.
    destruct (Nat.le_ge_cases n y).
    - apply (psi_L_mono y n H0) in H3.
      apply (CorSeq_sndOneOne (psi_L y) n); intuition.
      apply psi_L_CorSeq.
    - apply (psi_L_mono n y H0) in H.
      apply (CorSeq_sndOneOne (psi_L n) n); intuition.
      apply psi_L_CorSeq.
  Qed.

  Lemma pqiff_psi n:
    p n <-> q (psi_N n).
  Proof.
    unfold psi_N. 
    set (H:=proj2_sig (fstL_in_sig_nat n (psi_L n) (fst_psi_L_elem n))). cbn in H.
    apply (psi_L_CorSeq n), H.
  Qed.


  (* psi is an isomorphism *)

  Theorem MyhillH: 
    p == q.
  Proof.
    exists psi_N.
    split.
    - split.
      + exact inj_psi.
      + exact sur_psi.
    - exact pqiff_psi.
  Qed.

End Myhill.


(* Myhill's Isomorphism Theorem for predicates on natural numbers *)

Theorem Myhill_nat (p q: nat -> Prop): 
  p =1 q <-> (p == q).
Proof.
  split.
  - intros [[f1 H1] [f2 H2]]. exact (MyhillH p q f1 f2 H1 H2).
  - intros I. apply rec_iso_one_one_deg; intuition.
    + apply nat_datatype.
    + exact D_nat. 
Qed.


(* Myhill's Isomorphism Theorem for predicates on discrete types isomorphic to nat *)

Theorem Myhill {X Y} (p: X -> Prop) (q: Y -> Prop):
  type_iso nat X -> discrete X -> type_iso nat Y -> discrete Y -> p =1 q <-> (p == q).
Proof.
  intros [f1 BX] DX [f3 BY] DY.
  assert (enumerable_T X) as EX by (exists f1; apply BX).
  assert (enumerable_T nat) as EN by apply nat_datatype. 
  split.
  - set (p' := fun n => p (f1 n)).
    set (q' := fun n => q (f3 n)).
    assert (p' == p) by (exists f1; intuition).
    assert (q' == q) by (exists f3; intuition).
    intros H1. apply (rec_iso_trans q'); intuition.
    apply (rec_iso_trans p').
    + apply rec_iso_sym ; intuition.
    + apply Myhill_nat. apply (one_one_deg_trans p). 
      * now apply rec_iso_one_one_deg.
      * apply (one_one_deg_trans q); intuition.
        unfold one_one_degree. rewrite and_comm. 
        now apply rec_iso_one_one_deg.
  - intros H. now apply rec_iso_one_one_deg.
Qed.
