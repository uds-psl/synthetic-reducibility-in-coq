From Coq Require Import Arith Lia.

Require Import Preliminaries_Coq Preliminaries_Lists_Coq Definitions_Coq .

(* Preliminary Results regarding Corresponding Lists for Truth-Table Reductions *) 

Section Corresponding.

  Context {X: Type}.

  Variable (p: X -> Prop).

  Lemma corresponding_firstn LX1 LX2 LB1 LB2:  
    corresponding p (LX1 ++ LX2) (LB1 ++ LB2) -> length LX1 = length LB1 -> corresponding p LX1 LB1.
  Proof.
    revert LX1. induction LB1; intros LX1 H1 H2.
    - cbn in H2. apply length_zero_iff_nil in H2. 
      rewrite H2. constructor.
    - destruct LX1; cbn in H2; try discriminate.
      constructor.
      + now inversion H1.
      + apply IHLB1.
        * now inversion H1.
        * lia.
  Qed.

  Lemma corresponding_app  LX1 LX2 LB1 LB2:  
    corresponding p LX1 LB1 -> corresponding p LX2 LB2 -> corresponding p (LX1 ++ LX2) (LB1 ++ LB2).
  Proof.
    revert LX1. induction LB1; intros LX1 H1 H2; inversion H1. 
    - exact H2.
    - cbn; constructor; intuition.
      specialize (IHLB1 l). intuition.
  Qed.

  Lemma corresponding_rev LX LB:
    corresponding p LX LB -> corresponding p (rev LX) (rev LB).
  Proof.
    induction 1.
    - constructor.
    - cbn. apply corresponding_app; firstorder. 
      constructor; intuition.  
  Qed.

  Lemma corresponding_length  LX LB:
    corresponding p LX LB -> length LX = length LB.
  Proof.
    induction 1; firstorder. cbn; now rewrite IHForall2.
  Qed.

  Lemma corresponding_skipn LX1 LX2 LB1 LB2:  
    corresponding p (LX1 ++ LX2) (LB1 ++ LB2) -> length LX1 = length LB1 -> corresponding p LX2 LB2.
  Proof.
    intros H E. rewrite <- rev_involutive, <- (rev_involutive LX2).  
    apply corresponding_rev. apply corresponding_rev in H. 
    repeat rewrite rev_app_distr in H. 
    apply corresponding_firstn in H; intuition. 
    apply corresponding_length in H. 
    repeat rewrite app_length in H.
    repeat rewrite rev_length. repeat rewrite rev_length in H.
    lia.
  Qed.

  Lemma corresponding_compl1 LX LB:
    corresponding p LX LB -> corresponding (compl p) LX (map negb LB).
  Proof.  
    induction 1.
    - constructor.
    - cbn. constructor. 
      + split. 
        * intros npx. destruct y; firstorder. 
        * intros E px % H. 
          rewrite px in E; cbn; discriminate.
      + exact IHForall2.  
  Qed.

  Lemma corresponding_compl2 LX LB:
    stable p -> corresponding (compl p) LX LB -> corresponding p LX (map negb LB).
  Proof.
    intros S. induction 1.
    - constructor.
    - cbn; constructor.
      + split.
        * intros px. destruct y; firstorder. 
        * intros E. apply S. 
          intros npx % H. destruct y; firstorder; discriminate.
      + exact IHForall2.  
  Qed.

  Lemma corresponding_one_one LX LB1 LB2:
    corresponding p LX LB1 -> corresponding p LX LB2 -> LB1 = LB2.
  Proof.
    intros H1. revert LB2. 
    induction H1. 
    - intros LB2 H2. now inversion H2. 
    - intros LB2 H2. inversion H2. 
      specialize (IHForall2 l'0 H6). rewrite IHForall2.
      destruct y, y0; firstorder; discriminate. 
  Qed.

  Lemma corresponding_weak:
    forall L, ~~ exists LB, corresponding p L LB /\ length LB = length L.
  Proof.
    intros L. induction L.
    - intros H; apply H. 
      exists nil; firstorder. constructor.
    - intros H; apply IHL. 
      intros [LB C]. FalseDec (p a).
      + apply H. exists (true::LB). split. 
        * constructor; firstorder.
        * cbn; lia.
      + apply H. exists (false::LB). split.
        * constructor; firstorder. discriminate.
        * cbn; lia.
  Qed.

  Lemma corresponding_all_true L1 L2:
    corresponding p L1 L2 -> Forall (fun b : bool => b = true) L2 -> Forall p L1.
  Proof.
    intros H1 H2. induction H1.
    - constructor.
    - constructor. 
      + apply H. now inversion H2.
      + apply IHForall2. now inversion H2. 
  Qed.

  Lemma corresponding_all_p  L1 L2:
    corresponding p L1 L2 ->  Forall p L1 -> Forall (fun b : bool => b = true) L2.
  Proof.
    intros H1 H2. induction H1.
    - constructor.
    - constructor. 
      + apply H. now inversion H2.
      + apply IHForall2. now inversion H2. 
  Qed.

End Corresponding.