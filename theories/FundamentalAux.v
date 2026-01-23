

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl
    Util BasicAST Typing BasicMetaTheory Reduction LRDef LRBasicProps. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.

Lemma prefundamental_sort l : ⊩< Ax l > Sort l ≡ Sort l ↓ (fun A B => exists R, ⊩< l > A ≡ B ↓ R).
Proof.
    intros. eapply LR_U.
    1,2: eauto using val_redd_to_whnf, typing, ctx_nil.
    intros; split; eauto.
Qed.

Lemma helper_LR i A B :
    (exists R, ⊩< i > A ≡ B ↓ R) <->
    (exists R, ⊩< Ax i > Sort i ≡ Sort i ↓ R ∧ R A B).
Proof.
    split.
    - intros ϵAB.
      exists (fun A B => exists R, ⊩< i > A ≡ B ↓ R).
      split; eauto using prefundamental_sort.
    - intros ϵsort. destruct ϵsort as (R & ϵsort & ϵAB).
      unshelve eapply LR_ty_inv in ϵsort.
      shelve. eauto using  val_redd_to_whnf, typing, ctx_nil.
      destruct ϵsort as (_ & _ & _ & equiv). rewrite <- equiv. eauto.
Qed.


Lemma getLR_of_motive_aux {Γ i k A1 ϵA P1 P2 σ1 σ2} :
    ⊩< i > A1 <[σ1] ≡ A1 <[σ2] ↓ ϵA ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ⊩s σ1 ≡ σ2 : Γ ->
    let eP := eT (ty k) (P1 <[ (var 0) .: σ1 >> ren_term S]) (P2 <[ (var 0) .: σ2 >> ren_term S]) in
    ∀ (b1 b2 : term) (ϵb : ϵA b1 b2),
        (⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P1 <[ b2 .: σ2 ] ↓ eP b1 b2)
        /\ (⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P2 <[ b2 .: σ2 ] ↓ eP b1 b2)
        /\ (forall b3 (ϵb' : ϵA b1 b3), ⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P1 <[ b3 .: σ2 ] ↓ eP b1 b2).
Proof.
    intros.
    assert (⊩s (b1 .: σ1) ≡ (b2 .: σ2) : (Γ ,, (i, A1))) as ϵaσ.
    unshelve econstructor. exact ϵA. rasimpl. eauto. rasimpl. eauto.
    rasimpl. eauto.
    eapply H0 in ϵaσ as temp.  rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ & LR_Paσ).
    assert (Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P1 : Sort (ty k)) as LRv_P11 by eauto using LRv_sym, LRv_trans.
    eapply LRv_P11 in ϵaσ as temp. rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ' & LR_Paσ').
    split. eapply LR_iff_rel; eauto. eapply ϵT_iff_eT; eauto. rasimpl. eauto using LR_iff_rel, LR_irrel.
    split. eapply LR_iff_rel; eauto. eapply ϵT_iff_eT; eauto. rasimpl. eauto.
    intros.
    assert (⊩s (b1 .: σ1) ≡ (b3 .: σ2) : (Γ ,, (i, A1))) as ϵaσ'.
    unshelve econstructor. exact ϵA. rasimpl. eauto. rasimpl. eauto.
    rasimpl. eauto.
    eapply LRv_P11 in ϵaσ' as temp.  rewrite <- helper_LR in temp.
    destruct temp as (ϵPaσ'' & LR_Paσ'').
    eapply LR_iff_rel; eauto.  eapply ϵT_iff_eT; eauto.  rasimpl. eauto using LR_iff_rel, LR_irrel.
Qed.

Corollary getLR_of_motive {Γ i k A1 ϵA P1 P2 σ1 σ2} :
    ⊩< i > A1 <[σ1] ≡ A1 <[σ2] ↓ ϵA ->
    Γ,, (i, A1) ⊨< Ax (ty k) > P1 ≡ P2 : Sort (ty k) ->
    ⊩s σ1 ≡ σ2 : Γ ->
    exists eP,
        eP = eT (ty k) (P1 <[ (var 0) .: σ1 >> ren_term S]) (P2 <[ (var 0) .: σ2 >> ren_term S]) /\
        (∀ (b1 b2 : term) (ϵb : ϵA b1 b2), (⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P1 <[ b2 .: σ2 ] ↓ eP b1 b2)) /\
        (∀ (b1 b2 : term) (ϵb : ϵA b1 b2), (⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P2 <[ b2 .: σ2 ] ↓ eP b1 b2)) /\
        (∀ (b1 b2 b3 : term) (ϵb : ϵA b1 b2) (ϵb' : ϵA b1 b3), (⊩< ty k > P1 <[ b1 .: σ1 ] ≡ P1 <[ b3 .: σ2 ] ↓ eP b1 b2)).
Proof.
    intros. eexists. split. reflexivity.
    split. 2:split.
    all:intros; eapply getLR_of_motive_aux in ϵb as temp; eauto; destruct temp as (K1 & K2 & K3); eauto.
Qed.

Lemma LRv_to_LR_ty Γ A1 A2 i σ1 σ2 :
    ⊩s σ1 ≡ σ2 : Γ ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    exists ϵA, ⊩< i > A1<[σ1] ≡ A2<[σ2] ↓ ϵA.
Proof.
    intros ϵσ LRv_A12.
    eapply LRv_A12 in ϵσ.
    rewrite <- helper_LR in ϵσ.
    eauto.
Qed.

Lemma LRv_to_LR_ty_copy Γ A1 A2 A1' A2' ϵA i σ1 σ2 :
    ⊩s σ1 ≡ σ2 : Γ ->
    A1' = A1<[ σ1] ->
    ⊩< i > A1' ≡ A2' ↓ ϵA ->
    Γ ⊨< Ax i > A1 ≡ A2 : Sort i ->
    ⊩< i > A1<[σ1] ≡ A2<[σ2] ↓ ϵA.
Proof.
    intros ϵσ eq LR_A' LRv_A12. subst.
    eapply LRv_A12 in ϵσ.
    rewrite <- helper_LR in ϵσ.
    destruct ϵσ as (ϵA' & LR_A).
    eapply LR_iff_rel; eauto.
    eauto using LR_irrel.
Qed.

Lemma LRv_to_LR_tm Γ A1 A1' A2 ϵA i t1 t2 σ1 σ2 :
    ⊩s σ1 ≡ σ2 : Γ ->
    A1' = A1<[ σ1] ->
    ⊩< i > A1' ≡ A2 ↓ ϵA ->
    Γ ⊨< i > t1 ≡ t2 : A1 ->
    ϵA (t1<[σ1]) (t2<[σ2]).
Proof.
    intros ϵσ eq LR_A LRv_t12.
    subst.
    eapply LRv_t12 in ϵσ as temp.
    destruct temp as (ϵA' & LR_A' & ϵt).
    assert (ϵA <~> ϵA') as ϵA_iff_ϵA' by eauto using LR_irrel.
    rewrite ϵA_iff_ϵA'. eauto.
Qed.


Lemma substs_one_3 Γ l t u A :
  Γ ⊢d< l > t ≡ u : A ->
  Γ ⊢ds t .. ≡ u .. : (Γ ,, (l, A)).
Proof.
  intros.
  econstructor; rasimpl; eauto using refl_subst, subst_id, validity_ty_ctx, validity_conv_left.
Qed.

Lemma substs_one_4 Γ l l' t t' u u' A B :
  Γ ⊢d< l > t ≡ u : A ->
  Γ ⊢d< l' > t' ≡ u' : B ->
  Γ ⊢ds (t' .: t ..) ≡ (u' .: u ..) : (Γ ,, (l, A) ,, (l', S ⋅ B)).
Proof.
  intros.
  econstructor; rasimpl; eauto.
  econstructor; rasimpl; eauto using subst_id, refl_subst, validity_conv_left, validity_ty_ctx.
Qed.


Lemma subst_id_reduce1 : pointwise_relation _ eq (var 0 .: (S >> var)) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a; reflexivity.
Qed.

Lemma subst_id_reduce2 : pointwise_relation _ eq (var 0 .: (var 1 .: (S >> (S >> var)))) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a. reflexivity. destruct a. reflexivity. reflexivity.
Qed.
