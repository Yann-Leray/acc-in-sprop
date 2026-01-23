

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp 
    Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl Util BasicAST Typing BasicMetaTheory
    Reduction LRDef LRBasicProps FundamentalAux FundamentalPi FundamentalNat FundamentalAcc FundamentalCast.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.


Lemma fundamental_sort Γ l : ⊢d Γ -> Γ ⊨< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l).
Proof.
    intros Γ_Wt. unfold LRv. intros σ1 σ2 ϵσ12.
    eexists. split; eauto using prefundamental_sort. simpl. eexists. eauto using prefundamental_sort.
Qed.

Lemma fundamental_var Γ x k A :
    Γ ∋< ty k > x : A ->
    ⊢d Γ ->
    Γ ⊨< ty k > var x ≡ var x : A.
Proof.
    generalize Γ k A. clear Γ k A. induction x; unfold LRv; intros.
    - destruct Γ; dependent destruction H. dependent destruction H1.
      rasimpl. eauto.
    - destruct Γ; dependent destruction H. dependent destruction H1.
      eapply IHx in H as H'. 2:inversion H0; eauto.
      eapply H' in H1 as (R' & LR & lr).
      exists R'. split; rasimpl; eauto.
Qed.

Lemma fundamental_prop_ty Γ A B :
    Γ ⊢d< Ax prop > A ≡ B : Sort prop ->
    Γ ⊨< Ax prop > A ≡ B : Sort prop.
Proof.
    intros. unfold LRv. intros.
    rewrite <- helper_LR.
    eexists (fun t u => ∙ ⊢d< prop > t ≡ u : A <[ σ1]). eapply LR_prop.
    2: reflexivity.
    eapply LR_subst_escape in H0. eapply subst_conv in H; eauto.
    constructor.
Qed.

Lemma fundamental_prop Γ t u A :
    Γ ⊢d< prop > t ≡ u : A ->
    Γ ⊨< prop > t ≡ u : A.
Proof.
    intros. unfold LRv. intros σ1 σ2 ϵσ12.
    exists (fun t u => ∙ ⊢d< prop > t ≡ u : A <[ σ1]).
    split.
    2:eauto using subst_conv, LR_subst_escape.
    eapply LR_prop.
    2:reflexivity.
    eauto 8 using subst_conv, validity_conv_left, validity_ty_ty,
        conv_refl, LR_subst_escape, ctx_typing.
    eapply subst_conv; eauto using ctx_typing, LR_subst_escape.
Qed.


(* used to eliminate the condition
        forall k, l = ty k -> Γ ⊢d< l > t ≡ u : A -> ...
    from the IHs in the proof of fundamental_ty *)
Lemma helper_fund Γ l t u A :
    Γ ⊢d< l > t ≡ u : A ->
    (forall k, l = ty k -> Γ ⊢d< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A) <-> Γ ⊨< l > t ≡ u : A.
Proof.
    intros. split. intros.
    destruct l; eauto using fundamental_prop.
    eauto.
Qed.


Theorem fundamental_ty :
    (forall Γ l t A, Γ ⊢d< l > t : A -> forall k (_temp : l = ty k), Γ ⊢d< l > t ≡ t : A -> Γ ⊨< l > t ≡ t : A) /\
    (forall Γ l t u A, Γ ⊢d< l > t ≡ u : A -> forall k (_temp : l = ty k), Γ ⊢d< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A).
Proof.
    apply typing_mutind; intros.
    all: dependent destruction _temp.
    all: try erewrite helper_fund in *; eauto using conv_refl.
    - eauto using fundamental_var.
    - eauto using fundamental_sort.
    - destruct j. eauto using fundamental_pi, conv_refl. eauto using fundamental_prop_ty.
    - destruct j; dependent destruction H3. eauto using fundamental_lam, conv_refl.
    - eauto 6 using fundamental_app, conv_refl.
    - eauto using fundamental_nat.
    - eauto using fundamental_zero.
    - eauto using fundamental_succ, conv_refl.
    - eauto 6 using fundamental_rec, conv_refl.
    - eauto using fundamental_prop_ty.
    - eauto 9 using fundamental_accel, conv_refl.
    - eauto using fundamental_prop_ty.
    - eauto 6 using fundamental_cast, conv_refl.
    - eauto using fundamental_conv, conv_refl.
    - eauto using fundamental_var.
    - eauto using fundamental_sort.
    - destruct j. eauto using fundamental_pi. eauto using fundamental_prop_ty.
    - destruct j; dependent destruction H4. eauto using fundamental_lam.
    - eauto using fundamental_app.
    - eauto using fundamental_nat.
    - eauto using fundamental_zero.
    - eauto using fundamental_succ.
    - eauto 6 using fundamental_rec, conv_refl.
    - eauto using fundamental_prop_ty.
    - eauto using fundamental_accel.
    - eauto using fundamental_prop_ty.
    - eauto using fundamental_cast.
    - eauto using fundamental_cast_refl, conv_refl. 
    - eauto using fundamental_cast_pi.
    - eauto using fundamental_conv.
    - eauto using fundamental_beta.
    - destruct j. eauto using fundamental_eta. eauto using fundamental_prop.
    - eauto using fundamental_rec_zero.
    - eauto using fundamental_rec_succ.
    - eauto using fundamental_accel_accin.
    - unfold LRv. intros. eapply LR_subst_sym in H1. eapply H in H1 as (ϵA & LR_A & lr).
      eapply LR_sym in LR_A. eapply LR_sym_tm in lr; eauto.
    - unfold LRv. intros. assert (⊩s σ2 ≡ σ2 : Γ) by eauto using LR_subst_sym, LR_subst_trans.
      eapply H in H2 as (ϵA & LR_A & ϵtu). eapply H0 in H3 as (ϵA' & LR_A' & ϵuv).
      assert (ϵA <~> ϵA') by eauto using LR_sym, LR_irrel. rewrite <- H2 in ϵuv.
      eapply LR_trans_tm in ϵuv; eauto.
Qed.

Theorem fundamental Γ l t A : Γ ⊢d< l > t : A -> Γ ⊨< l > t ≡ t : A.
Proof.
    intros. destruct l.
    eapply (proj1 fundamental_ty) in H; eauto using conv_refl.
    eapply conv_refl in H. eapply fundamental_prop in H. eauto.
Qed.


Theorem fundamental_conv Γ l t u A : Γ ⊢d< l > t ≡ u : A -> Γ ⊨< l > t ≡ u : A.
Proof.
    intros. destruct l.
    eapply (proj2 fundamental_ty) in H; eauto using conv_refl.
    eapply fundamental_prop in H. eauto.
Qed.

Fixpoint mk_Nat k :=
    match k with
    | O => zero
    | S k => succ (mk_Nat k)
    end.

Lemma mk_nat_typed k : ∙ ⊢d< ty 0 > (mk_Nat k) : Nat.
Proof.
    intros. induction k; eauto using typing, ctx_typing.
Qed.

Lemma canonicity_helper t u : ϵNat t u -> exists k, ϵNat t (mk_Nat k).
Proof.
    intros. induction H.
    - exists O. eapply ϵzero; eauto using val_redd_to_whnf, typing, ctx_typing.
    - destruct IHϵNat as (k & ih). exists (S k).
      eapply ϵsucc; eauto using val_redd_to_whnf, mk_nat_typed, typing.
Qed.


(* we use the predicate ϵNat t (mk_Nat k) to encode the fact that
    t reduces in mutiple iterations to mk_Nat k *)
Corollary canonicity_red t :
    ∙ ⊢d< ty 0 > t : Nat -> exists k, ϵNat t (mk_Nat k).
Proof.
    intros. eapply fundamental in H; eauto. unfold LRv in H.
    destruct (H var var (LR_sempty _ _)) as (ϵnat' & LR_nat & ϵt).
    simpl in LR_nat.
    assert (ϵnat' <~> ϵNat) by eauto using LR_irrel, prefundamental_nat.
    rewrite H0 in ϵt. rasimpl in ϵt.
    eauto using canonicity_helper.
Qed.

Corollary canonicity_conv t :
    ∙ ⊢d< ty 0 > t : Nat -> exists k, ∙ ⊢d< ty 0 > t ≡ (mk_Nat k) : Nat.
Proof.
    intros. eapply canonicity_red in H as (k & lr).
    eauto using ϵNat_escape.
Qed.

Print Assumptions canonicity_conv.