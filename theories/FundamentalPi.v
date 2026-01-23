

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp
    Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl Util BasicAST 
    Typing BasicMetaTheory Reduction LRDef LRBasicProps FundamentalAux.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Lemma prefundamental_pi i A1 A2 k ϵA ϵB B1 B2 :
    ∙ ⊢d< Ax i > A1 ≡ A2 : Sort i ->
    ⊩< i > A1 ≡ A2 ↓ ϵA ->
    ∙ ,, (i, A1) ⊢d< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    (forall a1 a2 (ϵa : ϵA a1 a2), ⊩< ty k > B1 <[ a1..] ≡ B2 <[ a2..] ↓ ϵB a1 a2) ->
    let ϵpi := ϵPi i (ty k) A1 A2 ϵA B1 B2 ϵB in
    ⊩< Ru i (ty k) > Pi i (ty k) A1 B1 ≡ Pi i (ty k) A2 B2 ↓ ϵpi.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 ϵpi.
    eapply LR_pi'; eauto.
    split; eauto.
Qed.

Lemma fundamental_common_pi Γ σ1 σ2 i A1 A2 k B1 B2 :
    Γ ⊢d< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢d< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    ⊩s σ1 ≡ σ2 : Γ ->
    exists ϵA ϵB,
        let ϵpi := ϵPi i (ty k) (A1 <[ σ1]) (A2 <[ σ2]) ϵA
                (B1 <[ var 0 .: (σ1 >> ren_term S)]) (B2 <[ var 0 .: (σ2 >> ren_term S)]) ϵB in
        ⊩< i > A1 <[ σ1] ≡ A2 <[ σ2] ↓ ϵA /\
        (forall a1 a2 (ϵa : ϵA a1 a2), ⊩< ty k > B1 <[ a1 .: σ1] ≡ B2 <[ a2 .: σ2] ↓ ϵB a1 a2) /\
        ⊩< Ru i (ty k) > (Pi i (ty k) A1 B1)<[σ1] ≡ (Pi i (ty k) A2 B2)<[σ2] ↓ ϵpi.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 ϵσ12.

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_ty in LRv_A12 as temp; eauto. destruct temp as (ϵA & LR_A12).
    eapply LRv_to_LR_ty_copy in LRv_A11 as LR_A11; eauto.

    eapply getLR_of_motive in LRv_B12 as temp; eauto.
    destruct temp as (eB & eB_eq & LR_B11 & LR_B12 & LR_B11').

    exists ϵA. exists eB.
    split. eauto.
    split. eauto.
    unshelve eapply prefundamental_pi; eauto.
    - eauto using subst_conv, LR_subst_escape, ctx_nil.
    - eapply subst_conv ; eauto using ctx_typing, LR_escape_ty, validity_conv_left.
      eapply lift_subst;
      eauto using validity_conv_left, validity_ty_ctx, LR_subst_escape.
    - intros. rasimpl. eauto.
Qed.

Lemma fundamental_pi B1 B2 {Γ i k A1 A2} :
    Γ ⊢d< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢d< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊨< Ax (Ru i (ty k)) > Pi i (ty k) A1 B1 ≡ Pi i (ty k) A2 B2 : Sort (Ru i (ty k)).
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12.
    unfold LRv. intros σ1 σ2 ϵσ12.
    eapply fundamental_common_pi in ϵσ12 as temp; eauto.
    destruct temp as (ϵA & ϵB & _ & _ & LR_pi).
    eapply helper_LR.  eauto.
Qed.

Lemma fundamental_lam Γ i k A1 B1 t1 A2 B2 t2 :
    Γ ⊢d< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢d< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊢d< (ty k) > t1 ≡ t2 : B1 ->
    Γ,, (i, A1) ⊨< (ty k) > t1 ≡ t2 : B1 ->
    Γ ⊨< Ru i (ty k) > lam i (ty k) A1 B1 t1 ≡ lam i (ty k) A2 B2 t2 : Pi i (ty k) A1 B1.
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12 t1_conv_t2 LRv_t12.
    intros σ1 σ2 ϵσ12.

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11
        by eauto using LRv_sym, LRv_trans.
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11
        by eauto using LRv_sym, LRv_trans.

    eapply fundamental_common_pi in ϵσ12 as temp.
    3:eapply LRv_A11. 4:eapply LRv_B11. 2,3: eauto using validity_conv_left, conv_refl.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. split. eauto. split.
    - simpl. eapply meta_lvl_conv.
      eapply conv_lam; eauto 9 using subst_conv, LR_subst_escape, lift_subst, validity_conv_left, validity_ty_ctx, LR_escape_ty, ctx_typing.
      reflexivity.
    - intros.
      assert (⊩s (s1 .: σ1) ≡ (s2 .: σ2) : (Γ ,, (i, A1))) as ϵsσ by eauto using LR_subst, LR_iff_rel.
      eapply LRv_to_LR_tm in ϵsσ as ϵt'; eauto.
      eapply LR_irred_tm; eauto.
        (* from this point on, it's just technical manipulations to show that the beta redex reduces *)
      + eapply redd_step; eauto using redd_refl.
        eapply red_conv. eapply red_beta'; fold subst_term; eauto ; rasimpl.
        all:eauto 13 using conv_refl, subst_conv, LR_subst_escape,
            validity_subst_conv_left, validity_conv_left, lift_subst, validity_ty_ctx, LR_escape_tm, LR_escape_ty, ctx_typing.
        rasimpl. eauto 8 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, conv_refl, subst_conv, ctx_typing.
        rasimpl. eapply redd_refl. eauto 6 using LR_subst_escape, validity_subst_conv_left, validity_conv_left, conv_refl, subst_conv, ctx_typing.
      + eapply redd_step; eauto using redd_refl.
        eapply red_conv. simpl. eapply red_beta; fold subst_term; rasimpl.
        all:eauto 14 using  subst_conv, LR_subst_escape, LR_sym, lift_subst, validity_ty_ctx,
            validity_subst_conv_right, validity_conv_right, LR_escape_tm, refl_subst, ctx_typing, LR_escape_ty.

        rasimpl. eauto 9 using subst_conv, conv_refl, validity_conv_left, subst_sym, LR_subst_escape, ctx_typing, LR_escape_ty, validity_ty_ctx.
        rasimpl. eapply redd_refl. eauto using validity_conv_right, subst_conv, LR_subst_escape, ctx_typing, validity_ty_ctx.
Qed.


Lemma fundamental_app Γ i k A1 B1 t1 u1 A2 B2 t2 u2 :
    Γ ⊢d< Ax i > A1 ≡ A2 : Sort i ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    Γ,, (i, A1) ⊢d< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B2 : Sort (ty k) ->
    Γ ⊢d< Ru i (ty k) > t1 ≡ t2 : Pi i (ty k) A1 B1 ->
    Γ ⊨< Ru i (ty k) > t1 ≡ t2 : Pi i (ty k) A1 B1 ->
    Γ ⊢d< i > u1 ≡ u2 : A1 ->
    Γ ⊨< i > u1 ≡ u2 : A1 ->
    Γ ⊨< ty k > app i (ty k) A1 B1 t1 u1 ≡ app i (ty k) A2 B2 t2 u2 : B1 <[ u1..].
Proof.
    intros A1_conv_A2 LRv_A12 B1_conv_B2 LRv_B12
        t1_conv_t2 LRv_t12 u1_conv_u2 LRv_u12 σ1 σ2 ϵσ.

    assert (Γ ⊨< Ax i > A1 ≡ A1 : Sort i) as LRv_A11
        by eauto using LRv_sym, LRv_trans.
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > B1 ≡ B1 : Sort (ty k)) as LRv_B11
        by eauto using LRv_sym, LRv_trans.

    eapply fundamental_common_pi in LRv_B11 as temp. 3:exact LRv_A11. 2-4: eauto using validity_conv_left, conv_refl.
    destruct temp as (ϵA & ϵB & LR_A11 & LR_B11 & LR_pi).

    assert (Γ ⊨< i > u1 ≡ u1 : A1) as LRv_u11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_to_LR_tm in LRv_u11 as ϵu11; eauto.
    eapply LRv_to_LR_tm in LRv_u12 as ϵu12; eauto.

    eexists. split. rasimpl. unshelve eapply LR_B11; eauto.

    eapply LRv_t12 in ϵσ as temp. destruct temp as (ϵpi' & LR_pi' & ϵt).
    eassert (ϵpi' <~> ϵPi _ _ _ _ _ _ _ _) by eauto using LR_irrel.
    rewrite H in ϵt. destruct ϵt. rasimpl.
    assert (ϵB (u1 <[ σ1]) (u1 <[ σ2]) <~> ϵB (u1 <[ σ1]) (u2 <[ σ2]))
        as Hiff by eauto using LR_irrel.
    rewrite Hiff.

    eapply LR_app_ann_right; eauto.
    eapply subst_conv; eauto using ctx_typing, LR_escape_ty, validity_conv_right.
    eapply lift_subst; eauto 7 using LR_subst_escape, validity_subst_conv_right, validity_conv_left, validity_ty_ctx, refl_subst, ctx_typing.
    eapply subst_conv; eauto 7 using LR_subst_escape, validity_subst_conv_right, refl_subst, lift_subst, ctx_typing, validity_ty_ctx, validity_conv_left.
Qed.

Lemma fundamental_beta Γ i k A B t u :
    Γ ⊢d< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    Γ,, (i, A) ⊢d< Ax (ty k) > B : Sort (ty k) ->
    Γ,, (i, A) ⊨< Ax (ty k) > B ≡ B : Sort (ty k) ->
    Γ,, (i, A) ⊢d< ty k > t : B ->
    Γ,, (i, A) ⊨< ty k > t ≡ t : B ->
    Γ ⊢d< i > u : A ->
    Γ ⊨< i > u ≡ u : A ->
    Γ ⊨< ty k > app i (ty k) A B (lam i (ty k) A B t) u ≡ t <[ u..] : B <[ u..].
Proof.
    intros WtA LR_A WtB LR_B Wtt LR_t Wtu LR_u.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_lam in LR_t; eauto using conv_refl.
    eapply fundamental_app in LR_u; eauto using conv_refl, conv_lam.
    eapply LR_u in ϵσ as (ϵBu & LR_Bu & ϵbeta).
    exists ϵBu. split; eauto.
    eapply LR_redd_tm; eauto.
    eauto using LR_escape_tm, validity_conv_left, redd_refl.
    eapply LR_escape_tm in ϵbeta; eauto.
    eapply validity_conv_right in ϵbeta.
    eapply type_inv in ϵbeta. dependent destruction ϵbeta.
    eapply type_inv in t_Wt. dependent destruction t_Wt.
    eapply red_to_redd. rasimpl. rasimpl in conv_ty. eapply red_conv.
    2:eapply conv_sym;eauto.
    eapply red_beta'; eauto using conv_refl; rasimpl; reflexivity.
Qed.



Lemma fundamental_eta Γ i n A B t u :
    Γ ⊢d< Ax i > A : Sort i ->
    Γ ⊨< Ax i > A ≡ A : Sort i ->
    Γ,, (i, A) ⊢d< Ax (ty n) > B : Sort (ty n) ->
    Γ,, (i, A) ⊨< Ax (ty n) > B ≡ B : Sort (ty n) ->
    Γ ⊢d< Ru i (ty n) > t : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > t ≡ t : Pi i (ty n) A B ->
    Γ ⊢d< Ru i (ty n) > u : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > u ≡ u : Pi i (ty n) A B ->
    let t_app_x := app i (ty n) (S ⋅ A) (up_ren S ⋅ B) (S ⋅ t) (var 0) in
    let u_app_x := app i (ty n) (S ⋅ A) (up_ren S ⋅ B) (S ⋅ u) (var 0) in
    Γ,, (i, A) ⊢d< ty n > t_app_x ≡ u_app_x : B ->
    Γ,, (i, A) ⊨< ty n > t_app_x ≡ u_app_x : B ->
    Γ ⊢d< Ru i (ty n) > t ≡ u : Pi i (ty n) A B ->
    Γ ⊨< Ru i (ty n) > t ≡ u : Pi i (ty n) A B.
Proof.
    intros AWt LRv_A BWt LRv_B tWt LRv_t uWt LRv_u tx ux tx_conv_ux LRv_tx_ux t_conv_u.
    unfold LRv. intros σ1 σ2 ϵσ.
    eapply fundamental_common_pi in ϵσ as temp; eauto using conv_refl.
    destruct temp as (ϵA & ϵB & LR_A & LR_B & LR_pi).
    eexists. split;eauto.
    unfold ϵPi. split.
    - eapply subst_conv; eauto using LR_subst_escape, ctx_nil.
    - intros.
      assert (⊩s (s1 .: σ1) ≡ (s2 .: σ2) : (Γ ,, (i, A))) as ϵsσ by eauto using LR_subst.
      eapply LRv_to_LR_tm in LRv_tx_ux as ϵtx_ux; eauto.
      unfold tx, ux in ϵtx_ux. rasimpl in ϵtx_ux.
      eapply ϵtx_ux.
Qed.

