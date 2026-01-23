
From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl Util BasicAST Typing BasicMetaTheory Reduction LRDef. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Lemma ϵNat_escape t1 t2 : ϵNat t1 t2 -> ∙ ⊢d< ty 0 > t1 ≡ t2 : Nat.
Proof.
    intros. induction H; eauto 7 using redd_whnf_to_conv, conv_sym, conv_trans, conv_succ.
Qed.

(* escape lemma *)
Lemma LR_escape l A B R :
    ⊩< l > A ≡ B ↓ R -> ∙ ⊢d< Ax l > A ≡ B : Sort l /\ forall t u, R t u -> ∙ ⊢d< l > t ≡ u : A.
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. split.
      + destruct p. auto.
      + destruct p. intros. eapply H0. eauto.
    - intros. split.
      + eauto using redd_whnf_to_conv, conv_trans, conv_sym.
      + intros. rewrite H in H0.
        eauto using ϵNat_escape, redd_whnf_to_conv, conv_conv, conv_sym.
    - intros. split.
      + eauto using redd_whnf_to_conv, conv_trans, conv_sym.
      + intros. apply H0 in H1 as (R' & lr). apply H in lr as (t_eq_u & _). eauto 8 using redd_whnf_to_conv, conv_trans, conv_sym, conv_conv.
    - intros. destruct H0 as (H0 & H0'). split; auto.
      intros. eapply redd_whnf_to_conv in A1_red_pi, A2_red_pi.
      eapply conv_trans. eapply A1_red_pi. eapply conv_trans. 2:(eapply conv_sym; eapply A2_red_pi).
      eapply conv_pi'; eauto.
      intros. apply H in H2. destruct H2. eauto using conv_conv, redd_whnf_to_conv, conv_sym.
Qed.


(* we split the result in two, so we can use eauto with it *)
Corollary LR_escape_ty {l A B R} :
    ⊩< l > A ≡ B ↓ R -> ∙ ⊢d< Ax l > A ≡ B : Sort l.
Proof.
    intros. eapply LR_escape in H as (H1 & H2). eauto.
Qed.

Corollary LR_escape_tm  {l A B R t u }:
    ⊩< l > A ≡ B ↓ R -> R t u -> ∙ ⊢d< l > t ≡ u : A.
Proof.
    intros. eapply LR_escape in H as (H1 & H2). eauto.
Qed.

Hint Unfold val : core.

Definition LR_pi' i k l S1 S2 ϵS T1 T2 ϵT R :
    let A1 := Pi i (ty k) S1 T1 in
    let A2 := Pi i (ty k) S2 T2 in
    ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) ->
    ⊩< i > S1 ≡ S2 ↓ ϵS ->
    (forall s1 s2 (ϵs : ϵS s1 s2), ⊩< ty k > T1 <[ s1 ..] ≡ T2 <[ s2 ..] ↓ ϵT s1 s2) ->
    R <~> (ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT) ->
    l = Ru i (ty k) ->
    ⊩< l > A1 ≡ A2 ↓ R.
Proof.
    intros. subst.
    eapply LR_pi; eauto 9 using val_redd_to_whnf, LR_escape_ty, validity_conv_left, validity_conv_right, conv_ty_in_ctx_conv, type_pi.
Qed.

(* closure under anti-reduction *)
Lemma LR_irred l A B R :
    ⊩< l > A ≡ B ↓ R ->
    (forall A' B',
        ∙ ⊢d< Ax l > A' -->> A : Sort l ->
        ∙ ⊢d< Ax l > B' -->> B : Sort l ->
        ⊩< l > A' ≡ B' ↓ R)
    /\
    (forall t u t' u',
        ∙ ⊢d< l > t' -->> t : A ->
        ∙ ⊢d< l > u' -->> u : A ->
        R t u ->
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. split; intros.
      eapply LR_prop. 2:split;intros. all:try rewrite H0 in *.
      all: eauto 6 using redd_to_conv, conv_sym, conv_trans, conv_conv.
    - split; intros. eapply LR_nat; eauto using redd_comp_redd_whnf.
      rewrite H in *. destruct H2;
      eauto 8 using ϵzero, ϵsucc, redd_comp_redd_whnf, redd_conv, redd_whnf_to_conv, conv_sym.
    - split; intros. eapply LR_U; eauto using redd_comp_redd_whnf.
      setoid_rewrite H0 in H3. setoid_rewrite H0. destruct H3 as (R' & lr). exists R'.
      eapply H in lr as (K1 & K2). eapply K1; eauto using redd_whnf_to_conv, redd_conv.
    - split; intros. eapply LR_pi; eauto using redd_comp_redd_whnf.
      rewrite H in *. destruct H4. split.
      eapply redd_to_conv in H2, H3. eapply redd_whnf_to_conv in A1_red_pi.
      eapply conv_conv in H2, H3; eauto. eauto using conv_sym, conv_trans.
      intros. eapply (proj2 (H1 _ _ ϵs)); eauto.
      eauto 6 using redd_app, redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left.
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv, LR_escape_ty.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi', redd_whnf_to_conv, LR_escape_ty.
      eauto using LR_escape_tm, subst_conv, substs_one, conv_sym, ctx_nil.
Qed.

Lemma LR_irred_ty l A B A' B' R :
    ∙ ⊢d< Ax l > A' -->> A : Sort l ->
    ∙ ⊢d< Ax l > B' -->> B : Sort l ->
    ⊩< l > A ≡ B ↓ R ->
    ⊩< l > A' ≡ B' ↓ R.
Proof.
    intros. eapply LR_irred in H1 as (H1 & H2). eauto.
Qed.

Lemma LR_irred_tm l A B t u t' u' R :
    ⊩< l > A ≡ B ↓ R ->
    ∙ ⊢d< l > t' -->> t : A ->
    ∙ ⊢d< l > u' -->> u : A ->
    R t u ->
    R t' u'.
Proof.
    intros. eapply LR_irred in H as (H3 & H4). eauto.
Qed.


(* Closure under reduction. Usually now shown, but greatly simplifies
    the fundamental lemma proofs for beta, rec_zero, rec_succ, ... *)
Lemma LR_redd l A B R :
    ⊩< l > A ≡ B ↓ R ->
    (forall A' B',
        ∙ ⊢d< Ax l > A -->> A' : Sort l ->
        ∙ ⊢d< Ax l > B -->> B' : Sort l ->
        ⊩< l > A' ≡ B' ↓ R)
    /\
    (forall t u t' u',
        ∙ ⊢d< l > t -->> t' : A ->
        ∙ ⊢d< l > u -->> u' : A ->
        R t u ->
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. split; intros.
      eapply LR_prop. 2:split;intros. all:try rewrite H0 in *.
      all: eauto 6 using redd_to_conv, conv_sym, conv_trans, conv_conv.
    - split; intros. eapply LR_nat; eauto using iredd_comp_redd_whnf.
      rewrite H in *. destruct H2;
      eauto 8 using ϵzero, ϵsucc, iredd_comp_redd_whnf, redd_conv, redd_whnf_to_conv, conv_sym.
    - split; intros. eapply LR_U; eauto using iredd_comp_redd_whnf.
      setoid_rewrite H0 in H3. setoid_rewrite H0. destruct H3 as (R' & lr). exists R'.
      eapply H in lr as (K1 & K2). eapply K1; eauto using redd_whnf_to_conv, redd_conv.
    - split; intros. eapply LR_pi; eauto using iredd_comp_redd_whnf.
      rewrite H in *. destruct H4. split.
      eapply redd_to_conv in H2, H3. eapply redd_whnf_to_conv in A1_red_pi.
      eapply conv_conv in H2, H3; eauto. eauto using conv_sym, conv_trans.
      intros. eapply (proj2 (H1 _ _ ϵs)); eauto.
      eauto 6 using redd_app, redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left.
      eapply redd_conv. eapply redd_app; eauto 8 using redd_whnf_to_conv, redd_conv, LR_escape_tm, validity_conv_left, validity_conv_right, type_conv, LR_escape_ty.
      eapply redd_conv; eauto. eauto using conv_trans, conv_pi', redd_whnf_to_conv, LR_escape_ty.
      eauto using LR_escape_tm, subst_conv, substs_one, conv_sym, ctx_nil.
Qed.

Lemma LR_redd_ty l A B A' B' R :
    ∙ ⊢d< Ax l > A -->> A' : Sort l ->
    ∙ ⊢d< Ax l > B -->> B' : Sort l ->
    ⊩< l > A ≡ B ↓ R ->
    ⊩< l > A' ≡ B' ↓ R.
Proof.
    intros. eapply LR_redd in H1 as (H1 & H2). eauto.
Qed.

Lemma LR_redd_tm l A B t u t' u' R :
    ⊩< l > A ≡ B ↓ R ->
    ∙ ⊢d< l > t -->> t' : A ->
    ∙ ⊢d< l > u -->> u' : A ->
    R t u ->
    R t' u'.
Proof.
    intros. eapply LR_redd in H as (H3 & H4). eauto.
Qed.



Lemma ϵNat_erasure t1 t2 t1' t2' :
    ∙ ⊢d< ty 0 > t1 ~ t1' : Nat ->
    ∙ ⊢d< ty 0 > t2 ~ t2' : Nat ->
    ϵNat t1 t2 ->
    ϵNat t1' t2'.
Proof.
    intros. generalize t1' t2' H H0. clear t1' t2' H H0.
    induction H1; intros u1 u2 t1_sim_u1 t2_sim_u2.
    - eapply sim_left_redd_whnf in H; simpl; eauto.
      eapply sim_left_redd_whnf in H0; simpl; eauto.
      eapply ϵzero; eauto.
    - eapply sim_left_redd_whnf in H; simpl; eauto.
      eapply sim_left_redd_whnf in H0; simpl; eauto.
      eapply ϵsucc; eauto.
Qed.

(* Invariance under conv annotations, needed here because we're using a fully-annotated syntax. *)
Lemma LR_ann l A B R :
    ⊩< l > A ≡ B ↓ R ->
    (forall A' B',
        ∙ ⊢d< Ax l > A ~ A' : Sort l ->
        ∙ ⊢d< Ax l > B ~ B' : Sort l ->
        ⊩< l > A' ≡ B' ↓ R)
    /\
    (forall t u t' u',
        ∙ ⊢d< l > t ~ t' : A ->
        ∙ ⊢d< l > u ~ u' : A ->
        R t u ->
        R t' u').
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _).
    - intros. destruct p. split; intros.
        + eapply LR_prop.
            ++ eauto 6 using conv_sym, conv_trans, sim_to_conv.
            ++ intros. destruct (H0 t u). split; eauto using conv_conv, conv_sym, sim_to_conv.
        + destruct (H0 t' u'). destruct (H0 t u). eauto 8 using sim_to_conv, conv_trans, conv_sym.
    - intros. split; intros.
        + eapply sim_left_redd_whnf in A1_red_nat; eauto.
          eapply sim_left_redd_whnf in A2_red_nat; eauto.
          apply LR_nat; eauto.
        + rewrite H in *. eauto 7 using ϵNat_erasure, redd_whnf_to_conv, conv_sym, aconv_conv.
    - intros. split; intros.
        + apply LR_U; eauto using sim_left_redd, sim_sym, sim_left_redd_whnf.
        + rewrite H0 in *. destruct H3 as (R' & lr). destruct (H t u R' lr).
          apply redd_whnf_to_conv in A1_red_U as A1_conv_U.
          exists R'. eapply H3; eauto using aconv_conv, conv_sym.
    - intros. split; intros.
        + eapply sim_left_redd_whnf in A1_red_pi; eauto.
          eapply sim_left_redd_whnf in A2_red_pi; eauto.
          eapply LR_pi; eauto 6 using sim_left_redd, sim_sym, sim_to_conv, conv_trans, conv_sym.
        + rewrite H in *. destruct H4. apply redd_whnf_to_conv in A1_red_pi as A1_conv_pi. split.
            ++ eapply sim_to_conv, conv_conv in H2, H3; eauto.
               eauto using conv_sym, conv_trans.
            ++ intros.
               destruct (H1 s1 s2 ϵs). eapply H7; eauto.
               +++ eapply aconv_app; eauto 7 using validity_conv_left, conv_refl, LR_escape_tm, redd_whnf_to_conv, aconv_conv, LR_escape_ty.
               +++ eapply aconv_conv; eauto using LR_escape_tm, subst_conv, substs_one, conv_sym, ctx_nil.
                   eapply aconv_app; eauto 9 using validity_conv_right, conv_refl, conv_ty_in_ctx_ty, LR_escape_tm, LR_escape_ty, type_conv.
                   eauto using aconv_conv, redd_whnf_to_conv, conv_sym, conv_trans, conv_pi', LR_escape_ty.
Qed.


Lemma LR_app_ann_left l i j A B S1 S2 T1 T2 ϵA t u v:
    ⊩< l > A ≡ B ↓ ϵA ->
    ϵA (app i j S1 T1 t u) v ->
    ∙,, (i, S1) ⊢d< Ax j > T1 ≡ T2 : Sort j ->
    ∙ ⊢d< Ax i > S1 ≡ S2 : Sort i ->
    ϵA (app i j S2 T2 t u) v.
Proof.
    intros.
    eapply LR_escape_tm in H0 as H0'; eauto.
    eapply validity_conv_left in H0' as appWt.
    eapply validity_conv_right in H0' as vWt.
    eapply type_inv in appWt. dependent destruction appWt.
    subst.
    eapply LR_ann; eauto using aconv_refl.
    eapply aconv_app; eauto using aconv_refl.
Qed.

Lemma LR_app_ann_right l i j A B S1 S2 T1 T2 ϵA t u v:
    ⊩< l > A ≡ B ↓ ϵA ->
    ϵA v (app i j S1 T1 t u) ->
    ∙,, (i, S1) ⊢d< Ax j > T1 ≡ T2 : Sort j ->
    ∙ ⊢d< Ax i > S1 ≡ S2 : Sort i ->
    ϵA v (app i j S2 T2 t u).
Proof.
    intros.
    eapply LR_escape_tm in H0 as H0'; eauto.
    eapply validity_conv_right in H0' as appWt.
    eapply validity_conv_left in H0' as vWt.
    eapply type_inv in appWt. dependent destruction appWt.
    subst.
    eapply LR_ann; eauto using aconv_refl.
    eapply aconv_app; eauto using aconv_refl.
Qed.



Definition LR_inv_ty_statement l A1 A2 A1' R (A1_redd_A1' : ∙ ⊢d< Ax l > A1 -->>! A1' : Sort l) : Prop :=
    match A1' with
    | Nat =>
        l = ty 0 /\
        ∙ ⊢d< Ax (ty 0) > A1 -->>! Nat : Sort (ty 0) /\
        ∙ ⊢d< Ax (ty 0) > A2 -->>! Nat : Sort (ty 0) /\
        R <~> ϵNat
    | Sort l' =>
        l = Ax l' /\
        ∙ ⊢d< Ax (Ax l') > A1 -->>! Sort l' : Sort (Ax l') /\
        ∙ ⊢d< Ax (Ax l') > A2 -->>! Sort l' : Sort (Ax l') /\
        R <~> (fun B1 B2 => exists R', ⊩< l' > B1 ≡ B2 ↓ R')
    | Pi i (ty k) S1 T1 => exists S2 T2 ϵS ϵT,
        l = Ru i (ty k) /\
        ∙ ⊢d< Ax (Ru i (ty k)) > A1 -->>! Pi i (ty k) S1 T1 : Sort (Ru i (ty k)) /\
        ∙ ⊢d< Ax (Ru i (ty k)) > A2 -->>! Pi i (ty k) S2 T2 : Sort (Ru i (ty k)) /\
        ∙ ,, (i, S1) ⊢d< Ax (ty k) > T1 ≡ T2 : Sort (ty k) /\
        ⊩< i > S1 ≡ S2 ↓ ϵS /\
        (forall s1 s2 (ϵs : ϵS s1 s2), ⊩< ty k > T1 <[ s1 ..] ≡ T2 <[ s2 ..] ↓ ϵT s1 s2) /\
        R <~> ϵPi i (ty k) S1 S2 ϵS T1 T2 ϵT
    | _ => False
    end.

(* LR inversion for types in ty *)
Lemma LR_ty_inv {n A1 A2 A1' R} (A1_redd_A1' : ∙ ⊢d< Ax (ty n) > A1 -->>! A1' : Sort (ty n)) : ⊩< ty n > A1 ≡ A2 ↓ R -> LR_inv_ty_statement (ty n) A1 A2 A1' R A1_redd_A1'.
Proof.
    intro lr. remember (ty n) as l.
    generalize l A1 A2 R lr A1' A1_redd_A1' Heql. clear l A1 A2 R lr A1' A1_redd_A1' Heql.
    refine (LR_ind _ _ _ _ _); intros; dependent destruction Heql.
    - eapply redd_whnf_det in A1_red_nat as A1'_eq_Nat; eauto. subst.
      simpl. eauto.
    - eapply redd_whnf_det in A1_red_U as A1'_eq_U; eauto. subst.
      simpl. eauto.
    - eapply redd_whnf_det in A1_red_pi as A1'_eq_pi; eauto. subst.
      simpl. do 4 eexists.
      split; eauto.
      split; eauto.
Qed.

(* LR inversion for types in prop *)
Lemma LR_prop_inv {A2 A1 R} : ⊩< prop > A1 ≡ A2 ↓ R -> LRΩ A1 A2 R.
Proof.
    intro lr. remember prop as l.
    generalize l A1 A2 R lr Heql. clear l A1 A2 R lr Heql.
    refine (LR_ind _ _ _ _ _); intros; dependent destruction Heql.
    assumption.
Qed.


(* irrelevance *)
Lemma LR_irrel l A B B' R1 R2 :
    ⊩< l > A ≡ B ↓ R1 ->
    ⊩< l > A ≡ B' ↓ R2 ->
    forall t1 t2, R1 t1 t2 <-> R2 t1 t2.
Proof.
    intro lr1. generalize l A B R1 lr1 B' R2. clear l A B R1 lr1 B' R2.
    refine (LR_ind _ _ _ _ _).
    - intros. eapply LR_prop_inv in H. destruct p, H. destruct (H1 t1 t2), (H2 t1 t2). split; eauto.
    - intros. eapply (LR_ty_inv A1_red_nat) in H0 as (_ & _ & _ & H0). symmetry. rewrite H. auto.
    - intros. eapply (LR_ty_inv A1_red_U) in H1 as (_ & _ & _ & H'). rewrite H0. rewrite H'. split; eauto.
    - intros. eapply (LR_ty_inv A1_red_pi) in H2 as (S2' & T2' & ϵS' & ϵT' & l_eq & A1_red' & A2_red' & T_eq & LR_S' & LR_T' & R_eq).
      assert (ϵS <~> ϵS') by eauto.
      rewrite R_eq, H.
      split.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2, ϵS' s1 s2 -> ϵT s1 s2 <~> ϵT' s1 s2).
            { intros. eapply H1. rewrite H2. eauto. eauto. }
        eapply H5; eauto. eapply H2 in ϵs.
        eapply LR_app_ann_left. 2:eapply LR_app_ann_right.
        all:eauto using validity_conv_left, conv_refl, LR_escape_ty, conv_sym, conv_trans, conv_ty_in_ctx_conv.
      + intros. destruct H3. split. eauto. intros.
        assert (forall s1 s2, ϵS s1 s2 -> ϵT' s1 s2 <~> ϵT s1 s2).
            { intros. symmetry. eapply H1. eauto. eapply LR_T'. rewrite <- H2. eauto. }
        eapply H5; eauto.  eapply H2 in ϵs.
        eapply LR_app_ann_left. 2:eapply LR_app_ann_right.
        all:eauto using validity_conv_left, conv_refl, LR_escape_ty, conv_sym, conv_trans, conv_ty_in_ctx_conv.
Qed.


Definition PER {A} (R:A -> A -> Prop) :=
    (forall t u, R t u -> R u t) /\ (forall t u v, R t v -> R v u -> R t u).

Lemma PER_refl {A} {R : A -> A -> Prop} {t u} : PER R -> R t u -> R t t.
Proof.
    intros. destruct H. eapply H1; eauto.
Qed.

(* Invariance under relations which are equivalent *)
Lemma LR_iff_rel l A B R R' :
    R <~> R' ->
    ⊩< l > A ≡ B ↓ R ->
    ⊩< l > A ≡ B ↓ R'.
Proof.
    intros. generalize l A B R H0 R' H. clear l A B R H0 R' H.
    refine (LR_ind _ _ _ _ _); intros.
    - eapply LR_prop; destruct p; eauto. intros. rewrite <- H. eauto.
    - eapply LR_nat; eauto. intros. rewrite <- H0. eauto.
    - eapply LR_U; eauto. intros. rewrite <- H1. eauto.
    - eapply LR_pi; eauto. intros. rewrite <- H2. eauto.
Qed.



(* there are different ways to prove the basic properties of the LR
    TODO finish writing this
   1) Prove all the properties together, using Angiuli's 'power move' as described in
        page 26 of the technical report for "Implementing a modal dependent type theory"
        (...)

   2) Jason Hu's Mctt : Changing the def of the logical relation, so that the fact that
        ϵS is a PER is built in
   3) MLTT à la Coq & Jason Hu's MINT:
        Prove first weaker statements and prove the real statements after.
        For instance, weakened symmetry then becomes
          ⊩< l > A ≡ B ↓ R -> exists R', ⊩< l > B ≡ A ↓ R' /\ forall t u, R t u -> R' u t
        However, when placing the logical relation in Prop, this seems
        to require eliminating from Prop to Type.
        Indeed, in the case of Pi, the ih of the codomain T gives
          forall s1 s2 (ϵs : ϵS s1 s2), exists ϵT', ...
        But we would need some form of choice to extract
          ϵT' : forall s1 s2 (ϵs : ϵS s1 s2), TmRel
        Thankfully, in McTT a way to sidestep the need of choice is given
        (altough they do not use it specifically for deriving the basic properties,
        as already mentioned). This is given by the following eT construction,
        along with the lemma ϵT_iff_eT stating that eT corresponds to the right
        relation ϵT, whenever we have enough information to obtain ϵT.
   *)


Definition eT j T1 T2 :=
    fun s1 s2 a1 a2 => forall R, ⊩< j > T1 <[ s1..] ≡ T2 <[ s2..] ↓ R -> R a1 a2.

Lemma ϵT_iff_eT i j S1 S2 ϵS T1 T2 ϵT s1 s2 :
    ⊩< i > S1 ≡ S2 ↓ ϵS ->
    ⊩< j > T1 <[ s1..] ≡ T2 <[ s2..] ↓ ϵT->
    ϵT <~> eT j T1 T2 s1 s2.
Proof.
    intros; split; intros.
    - unfold eT. intros. assert (R <~> ϵT) by eauto using LR_irrel.
      rewrite H3. eauto.
    - eapply H1 in H0. eauto.
Qed.

Opaque eT.

(* TODO: maybe factorize the construction of eT through the following choice principle,
    to enhance explainability of the construction? *)
Lemma choice A B R :
    (forall x : A, exists P : B x -> Prop, R x P) ->
    (forall x P Q, R x P -> R x Q -> forall b, P b -> Q b) ->
    (forall x P Q, (forall b, P b -> Q b ) ->
        R x P -> R x Q) ->
    @sig (forall x, B x -> Prop) (fun P => forall x, R x (P x)).
Proof.
    intros.
    unshelve econstructor.
    exact (fun a b => forall P, R a P -> P b).
    intros. destruct (H x).
    eapply H1. 2:exact H2.
    intros.
    eapply H0. exact H2. all:eauto.
Qed.


Lemma split_iff (R R': TmRel) : R <~> R' -> (forall t u, R t u -> R' t u) /\ (forall t u, R' t u -> R t u).
Proof.
    split; intros; rewrite H in *; eauto.
Qed.




Lemma ϵNat_sym t1 t2 :
    ϵNat t1 t2 ->
    ϵNat t2 t1.
Proof.
    intros.
    induction H.
    - eapply ϵzero; eauto.
    - eapply ϵsucc; eauto.
Qed.

(* We first need to show a weaker form of symmetry *)
Lemma LR_sym' l A B R :
    ⊩< l > A ≡ B ↓ R -> exists R', ⊩< l > B ≡ A ↓ R' /\ forall t u, R t u <-> R' u t.
Proof.
    generalize l A B R. clear l A B R.
    refine (LR_ind _ _ _ _ _); intros.
    - destruct p. exists R.
      split.
      + eapply LR_prop; eauto using conv_sym.
        setoid_rewrite H0. split; eauto using conv_conv, conv_sym.
      + setoid_rewrite H0. split; eauto using conv_sym.
    - eexists. split.
      + eapply LR_nat; eauto.
      + setoid_rewrite H. intros. split; eauto using ϵNat_sym.
    - exists (fun A B => exists R, ⊩< l > A ≡ B ↓ R).
      split.
      + eapply LR_U; eauto. split; eauto.
      + intros B1 B2; split; intros LR_B; rewrite H0 in *.
        all: destruct LR_B as (R' & LR_B); eapply H in LR_B as (R'' & LR_B' & _); eauto.
    - destruct H0 as (ϵS' & LR_S' & ϵS_iff_ϵS').
      eapply split_iff in ϵS_iff_ϵS' as (ϵS_to_ϵS' & ϵS'_to_ϵS).
      exists (ϵPi i (ty k) S2 S1 ϵS' T2 T1 (eT (ty k) T2 T1)).
      split.
      + eapply LR_pi; eauto using conv_sym, conv_ty_in_ctx_conv, LR_escape_ty.
        intros. apply ϵS'_to_ϵS in ϵs as ϵs'.
        destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT').
        eapply LR_iff_rel; eauto using ϵT_iff_eT.
        split; eauto.
      + intros; split; intros; rewrite H in *.
        ++  destruct H0. split; eauto using conv_pi', conv_sym, conv_conv, LR_escape_ty.
            intros.  apply ϵS'_to_ϵS in ϵs as ϵs'.
            destruct (H1 _ _ ϵs') as (ϵT' & LR_T' & ϵT_iff_ϵT').
            rewrite <- ϵT_iff_eT; eauto. rewrite <- ϵT_iff_ϵT'. eauto.
        ++  destruct H0. split; eauto 6 using conv_pi', conv_sym, conv_conv, LR_escape_ty.
            intros.
            destruct (H1 _ _ ϵs) as (ϵT' & LR_T' & ϵT_iff_ϵT').
            eapply H2 in LR_T'; eauto. rewrite ϵT_iff_ϵT'. eauto.
Qed.



Lemma ϵNat_trans t1 t2 t3 :
    ϵNat t1 t2 ->
    ϵNat t2 t3 ->
    ϵNat t1 t3.
Proof.
    intro. generalize t3. clear t3. induction H; intros.
    - dependent destruction H1.
        + eapply ϵzero; eauto.
        + eapply redd_whnf_det in H0; eauto. inversion H0.
    - dependent destruction H2.
        + eapply redd_whnf_det in H0; eauto. inversion H0.
        + eapply redd_whnf_det in H0; eauto.
          dependent destruction H0.
          eapply ϵsucc; eauto.
Qed.

(* And we also first need to show a weaker form of transitivity *)
Lemma LR_trans' l A B C R R' :
    ⊩< l > A ≡ B ↓ R -> ⊩< l > B ≡ C ↓ R' -> exists R'', ⊩< l > A ≡ C ↓ R'' /\ forall t v u, R t v -> R' v u -> R'' t u.
Proof.
    intro lr. generalize l A B R lr C R'. clear l A B R lr C R'.
    refine (LR_ind _ _ _ _ _); intros.
    - eapply LR_prop_inv in H. destruct H. destruct p.
      exists R. split.
      + eapply LR_prop; eauto using conv_trans.
      + intros. rewrite H2 in H3. rewrite H2. rewrite H0 in H4.
        eauto using conv_trans, conv_conv, conv_sym.
    - unshelve eapply LR_ty_inv in H0 as temp. 2:eauto.
      destruct temp as (_ & _ & C_red & H').
      eexists. split.
      + eapply LR_nat; eauto.
      + intros. rewrite H in *. rewrite H' in *. eauto using ϵNat_trans.
    - unshelve eapply LR_ty_inv in H1 as temp. 2:eauto.
      destruct temp as (_ & _ & C_red & H').
      exists (fun A B => exists R, ⊩< l > A ≡ B ↓ R).
      split.
      + eapply LR_U; eauto. split; eauto.
      + intros. rewrite H0 in H2. rewrite H' in H3.
        destruct H2. destruct H3.
        eapply H in H3; eauto.
        destruct H3 as (R'' & LR & _).
        eexists. eauto.
    - unshelve eapply LR_ty_inv in H2. 2: eauto.
      destruct H2 as (S' & T' & ϵS' & ϵT' & _ & _ & C_red & T2_eq_T' & LR_S' & LR_T' & R'_iff).
      pose proof LR_S' as temp. eapply H0 in temp as (ϵS'' & LR_S'' & ϵS_to). clear H0.

      (* we first show that the ϵS, ϵS', ϵS'' are all equivalent *)
      assert (ϵS <~> ϵS'') as _temp by eauto using LR_irrel.
      eapply split_iff in _temp as (ϵS_to_ϵS'' & ϵS''_to_ϵS).

      eapply LR_sym' in LR_S'' as temp. destruct temp as (ϵSc & LR_Sc & ϵSc_to).
      eapply LR_sym' in LR_S' as temp. destruct temp as (ϵSc' & LR_Sc' & ϵSc_to').
      assert (ϵSc <~> ϵSc') as _temp by eauto using LR_irrel.
      setoid_rewrite _temp in ϵSc_to. setoid_rewrite <- ϵSc_to in ϵSc_to'.
      eapply split_iff in ϵSc_to' as (ϵS'_to_ϵS'' & ϵS''_to_ϵS').
      clear ϵSc ϵSc' LR_Sc LR_Sc' _temp ϵSc_to.

      (* finally, we show that ϵS is symmetric *)
      eapply LR_sym' in LR_S as temp. destruct temp as (ϵSc & LR_Sc & ϵSc_to).
      assert (ϵSc <~> ϵS') by eauto using LR_irrel. setoid_rewrite H0 in ϵSc_to.
      eapply split_iff in ϵSc_to as (temp1 & temp2).
      assert (forall t u, ϵS t u -> ϵS u t) as ϵS_sym by eauto.
      clear ϵSc LR_Sc H0 temp1 temp2.

      exists (ϵPi i (ty k) S1 S' ϵS'' T1 T' (eT (ty k) T1 T')).
      split.
      + eapply LR_pi; eauto using conv_trans, conv_ty_in_ctx_conv, conv_sym, LR_escape_ty.
        intros. assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. eapply LR_T' in ϵs'' as LR_T_2.
        unshelve eapply H1 in LR_T_2. 3:eauto.
        destruct LR_T_2 as (ϵT'' & LR_T'' & ϵT_to).
        eapply LR_iff_rel. 2:eauto.
        eapply ϵT_iff_eT; eauto.
        split; eauto.
      + intros. rewrite H, R'_iff in *.
        destruct H0, H2.
        split; eauto 6 using conv_trans, conv_conv, conv_sym, conv_pi', conv_ty_in_ctx_conv, LR_escape_ty.
        intros.
        assert (ϵS s1 s2) as ϵs' by eauto. pose (LR_T_1 := LR_T _ _ ϵs').
        assert (ϵS' s2 s2) as ϵs'' by eauto. pose (LR_T_2 := LR_T' _ _ ϵs'').
        unshelve eapply H1 in LR_T_2. 3: eauto.
        destruct LR_T_2 as (ϵT'' & LR_T'' & ϵT_to).
        rewrite <- ϵT_iff_eT; eauto. eauto.
Qed.

(* We now derive the real refl, sym and trans *)

Lemma LR_refl_r l A B R : ⊩< l > A ≡ B ↓ R -> ⊩< l > B ≡ B ↓ R.
Proof.
    intros. eapply LR_sym' in H as temp.
    destruct temp as (R' & H' & X).
    eapply LR_trans' in H as (R'' & H'' & _); eauto.
    assert (R' <~> R'') by eauto using LR_irrel.
    eapply LR_sym' in H'' as (R''' & H''' & Y).
    eapply LR_iff_rel; eauto.
    setoid_rewrite X. setoid_rewrite <- Y.
    symmetry. eauto.
Qed.

Lemma LR_sym l A B R :
    ⊩< l > A ≡ B ↓ R -> ⊩< l > B ≡ A ↓ R.
Proof.
    intros.
    eapply LR_refl_r in H as ϵB_B.
    eapply LR_sym' in H as (R' & ϵB_A & equiv1).
    eapply LR_iff_rel; eauto using LR_irrel.
Qed.


(* Here we have a more general statement, in which we do not require R = R',
   and which is more convenient in some cases. However, thanks to LR_sym, LR_iff_rel
   and LR_irrel, the two are interderivable. *)
Lemma LR_trans l A B C R R' :
    ⊩< l > A ≡ B ↓ R -> ⊩< l > B ≡ C ↓ R' -> ⊩< l > A ≡ C ↓ R.
Proof.
    intros.
    eapply LR_trans' in H0; eauto.
    destruct H0 as (R'' & lr & _).
    eapply LR_iff_rel; eauto using LR_irrel.
Qed.

Lemma LR_sym_tm {l A B R t u} : ⊩< l > A ≡ B ↓ R -> R t u -> R u t.
Proof.
    intros. eapply LR_sym' in H as temp.
    destruct temp as (R' & lr & equiv).
    eapply LR_refl_r in H.
    assert (R <~> R') by eauto using LR_irrel.
    rewrite H1. eapply equiv in H0. eauto.
Qed.

Lemma LR_trans_tm {l A B R t u v} :
    ⊩< l > A ≡ B ↓ R ->
    R t v -> R v u -> R t u.
Proof.
    intros. eapply LR_refl_r in H as H'.
    eapply LR_trans' in H' as temp; eauto.
    destruct temp as (R' & lr & imp).
    assert (R <~> R') by eauto using LR_irrel.
    setoid_rewrite <- H2 in imp.
    eauto.
Qed.




(* escape lemma for subst reducibility *)
Lemma LR_subst_escape σ τ Δ : ⊩s σ ≡ τ : Δ -> ∙ ⊢ds σ ≡ τ : Δ.
Proof.
    intro. induction H. eauto using ConvSubst.
    eapply LR_escape_tm in H1; eauto. eauto using ConvSubst.
Qed.


(* subst reducibility is a PER *)

Lemma LR_subst_sym σ τ Δ : ⊩s σ ≡ τ : Δ -> ⊩s τ ≡ σ : Δ.
Proof.
    intros. induction H. eauto using LR_subst.
    eapply LR_sym_tm in H1; eauto. eapply LR_sym in H0. eauto using LR_subst.
Qed.

Derive Signature for LR_subst.

Lemma LR_subst_trans σ τ θ Δ : ⊩s σ ≡ τ : Δ -> ⊩s τ ≡ θ : Δ -> ⊩s σ ≡ θ : Δ.
Proof.
    intros. generalize θ H0. clear θ H0. induction H. eauto using LR_subst.
    intros. dependent destruction H2.
    assert (R <~> R0) by eauto using LR_irrel, LR_sym.
    rewrite <- H5 in H4.
    eapply LR_trans_tm in H4; eauto.
    eapply LR_trans in H3; eauto.
    eauto using LR_subst.
Qed.


(* We prove that validity is a PER *)

Lemma LRv_sym Γ l t u A : Γ ⊨< l > t ≡ u : A -> Γ ⊨< l > u ≡ t : A.
Proof.
    intros ϵtu. unfold LRv. intros σ1 σ2 ϵσ12.
    destruct (ϵtu _ _ ϵσ12) as (R & ϵA & ϵt). exists R. split; auto.
    eapply LR_subst_sym in ϵσ12 as ϵσ21. destruct (ϵtu _ _ ϵσ21) as (R' & ϵA' & ϵt').
    eapply LR_sym_tm in ϵt'; eauto. eapply LR_sym in ϵA'.
    eapply LR_irrel in ϵA; eauto. eapply ϵA. auto.
Qed.

Lemma LRv_trans Γ l t u v A : Γ ⊨< l > t ≡ v : A -> Γ ⊨< l > v ≡ u : A -> Γ ⊨< l > t ≡ u : A.
Proof.
    intros ϵtv ϵvu. unfold LRv. intros σ1 σ2 ϵσ12.
    destruct (ϵtv _ _ ϵσ12) as (R & ϵA & ϵt).
    assert (⊩s σ2 ≡ σ2 : Γ) as ϵσ22 by eauto using LR_subst_trans, LR_subst_sym.
    destruct (ϵvu _ _ ϵσ22) as (R' & ϵA' & ϵt').
    assert (R <~> R') as R_iff_R' by eauto using LR_irrel, LR_sym.
    exists R. split; eauto. rewrite <- R_iff_R' in ϵt'.
    eapply LR_trans_tm; eauto.
Qed.


