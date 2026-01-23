From Stdlib Require Import Utf8 List Arith Bool Lia.
From AccInSProp Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Typing BasicMetaTheory CompCanonicity Fundamental CHeqProps CDecoration.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.


(* Potential translations *)

Definition tr_ctx Γ Δ :=
  ⊢p Δ ∧ Γ ⊂ Δ.

Definition tr_ty_data l t A Γ' t' A' :=
  Γ' ⊢p< l > t' : A' ∧ t ⊏ t' ∧ A ⊏ A'.

Notation "D ⊨⟨ l ⟩ t : A ↦ u : B" :=
  (tr_ty_data l t A D u B)
  (at level 50, t, A, u, B at next level).

Definition tr_ty_abs l t A Γ' A' :=
  ∃ t', tr_ty_data l t A Γ' t' A'.

Notation "D ⊨⟨ l ⟩ t : A ⇒ B" :=
  (tr_ty_abs l t A D B)
  (at level 50, t, A, B at next level).

Definition tr_ty l t A Γ' :=
  ∃ A', Γ' ⊨⟨ l ⟩ t : A ⇒ A'.

Notation "D ⊨⟨ l ⟩ t : A" :=
  (tr_ty l t A D)
  (at level 50, t, A at next level).


(* Type heads *)

Inductive type_head := hSort (l : level) | hPi | hNat | hacc | hobseq.

Inductive has_type_head : term → type_head → Prop :=
| isSort l : has_type_head (Sort l) (hSort l)
| isPi i j A B : has_type_head (Pi i j A B) hPi
| isNat : has_type_head Nat hNat
| isacc i A R x : has_type_head (acc i A R x) hacc
| isobseq i A u v : has_type_head (obseq i A u v) hobseq.

Lemma keep_head_ty_aux Γ l A t h u :
  t ⊏ u ->
  Γ ⊢p< l > u : A -> 
  has_type_head t h ->
  exists B e v, 
    t ⊏ v /\
    has_type_head v h /\
    Γ ⊢p< l > v : B /\
    Γ ⊢p< prop > e : heq l A B u v.
Proof.
  intros. induction H1.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx, decoration.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H1. dependent destruction H1. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx. 
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H0. dependent destruction H0. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eapply conv_conv; eauto using conv_sym.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
    + eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
  - generalize Γ l A H0. clear Γ l A H0. dependent induction H; intros.
    + eapply type_inv in H2. dependent destruction H2. subst.
      eexists. eexists. eexists. 
      Unshelve. 4:exact (obseq (ty n) A' a' b'). 2,3:shelve.  
      intuition eauto using has_type_head, typing, validity_conv_left, validity_ty_ctx.
      1:econstructor; eauto.
      eapply type_conv. 2:eapply conv_heq.
      1:eapply type_heq_refl. 1:eauto using validity_conv_left.
      1:eapply type_conv. 2:eauto using conv_sym. 4,5:eapply conv_refl.
      all :eauto using conv_refl, validity_conv_left, validity_ty_ctx, typing.
      all:eauto using typing, conv_sym.
    +  eapply type_inv in H0. dependent destruction H0.
      eapply IHdecoration in a_Wt as temp.
      destruct temp as (B' & e' & v' & has_head & v_Wt & e'_Wt). subst.
      eexists. eexists. eexists. intuition eauto.
      eapply type_heq_trans. 5:eauto.
      4:eapply type_conv.
      4:eapply type_heq_sym, type_heq_cast.
      10:eapply conv_heq. 12:eapply conv_refl.
      all:eauto using conv_refl, conv_sym, typing.
Qed.

Lemma keep_head_ty Γ l A A0 h :
  A0 ⊏ A ->
  Γ ⊢p< Ax l > A : Sort l -> 
  has_type_head A0 h ->
  exists B e, 
    A0 ⊏ B /\
    has_type_head B h /\
    Γ ⊢p< prop > e : obseq (Ax l) (Sort l) A B.
Proof.
  intros. eapply keep_head_ty_aux in H1; eauto.
  destruct H1 as (B & e & v & refines & has_head & v_Wt & e_Wt).
  dependent destruction has_head;
  eapply type_inv in v_Wt; dependent destruction v_Wt.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - dependent destruction lvl_eq. destruct l; dependent destruction H1.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo; eauto using typing, validity_ty_ctx.
  - eapply Ax_inj in lvl_eq. subst.
    eexists. eexists. intuition eauto using has_type_head.
    eapply type_conv in e_Wt. 
    2:eapply conv_heq.  2:eapply conv_refl. 3:eauto using conv_sym.
    4:eapply conv_refl.
    2-4:eauto 8 using typing, conv_refl, validity_ty_ctx, conv_sym.
    eapply type_hetero_to_homo. 3:eapply e_Wt. all:eauto using typing, validity_ty_ctx.
Qed.


Lemma keep_head Γ' l t A h :
  Γ' ⊨⟨ l ⟩ t : A →
  has_type_head A h →
  ∃ A',
    has_type_head A' h ∧
    Γ' ⊨⟨ l ⟩ t : A ⇒ A'.
Proof.
  intros ht hh.
  destruct ht. destruct H. destruct H. destruct H0.
  eapply validity_ty_ty in H as H'.
  eapply keep_head_ty in hh; eauto.
  destruct hh as (B & e & refines & has_head & e_Wt).
  eexists. split; eauto.
  econstructor. econstructor. 
  1:eapply type_cast.
  3:eapply e_Wt.
  3:eauto.
  3:intuition eauto using decoration.
  all:eapply validity_ty_ty, type_inv in e_Wt; dependent destruction e_Wt; eauto.
Qed.

Corollary keep_sort Γ' i j A :
  Γ' ⊨⟨ i ⟩ A : Sort j →
  Γ' ⊨⟨ i ⟩ A : Sort j ⇒ Sort j.
Proof.
  intros h.
  eapply keep_head in h. 2: econstructor.
  destruct h as (A' & h & hA).
  inversion h. subst.
  assumption.
Qed.

Lemma change_type Γ' i t A A' :
  Γ' ⊨⟨ i ⟩ t : A →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ' ⊨⟨ i ⟩ t : A ⇒ A'.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H1.
  destruct H0. destruct H3.
  assert (x ~ A') by eauto using dec_to_sim, sim_trans, sim_sym.
  eapply validity_ty_ty in H as x_Wt.
  eapply sim_heq_same_ctx in H5; eauto.
  destruct H5.
  eapply type_hetero_to_homo in H5; eauto.
  eapply type_cast in H. 4:eapply H5.
  2,3:eauto.
  econstructor. econstructor.
  1:eauto.
  split; eauto using decoration.
Qed.

(* Translation of derivations *)

Lemma tr_meta Γ' i j t t' A A' B B' :
  Γ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  i = j →
  A = B →
  A' = B' →
  Γ' ⊨⟨ j ⟩ t : B ↦ t' : B'.
Proof.
  intros h -> -> ->. assumption.
Qed.

Lemma tr_ctx_inv Γ l A Δ :
  tr_ctx (Γ ,, (l, A)) Δ →
  ∃ Γ' A', tr_ctx Γ Γ' ∧ A ⊏ A' ∧ Δ = Γ',, (l, A').
Proof.
  intros [h1 h2].
  eapply Forall2_inv_l in h2 as ((l' & A') & Γ' & ? & (e & ?) & ->).
  cbn in e. subst.
  inversion h1. subst.
  firstorder eauto.
Qed.

Lemma varty_trans Γ Γ' x l A :
  Γ ∋< l > x : A →
  tr_ctx Γ Γ' →
  ∃ A', Γ' ∋< l > x : A' ∧ A ⊏ A'.
Proof.
  intros hx hc.
  induction hx as [| Γ i j A B x hx ih] in Γ', hc |- *.
  - eapply tr_ctx_inv in hc as (Δ & A' & hc & hA & ->).
    eexists. split.
    + constructor.
    + apply rename_dec. assumption.
  - eapply tr_ctx_inv in hc as (Δ & B' & hc & hB & ->).
    eapply ih in hc. destruct hc as (A' & h & hA).
    eexists. split.
    + econstructor. eassumption.
    + apply rename_dec. assumption.
Qed.

Lemma tr_var_known Γ Γ' x A A' l :
  Γ ∋< l > x : A →
  Γ' ∋< l > x : A' →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A ↦ var x : A'.
Proof.
  intros hx hx1 hc.
  eapply varty_trans in hx as hx2. 2: eassumption.
  destruct hx2 as (A'' & hx2 & hA).
  eapply varty_unique in hx1 as e. 2: eassumption.
  subst.
  split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
Qed.

Lemma tr_var Γ Γ' x A l :
  Γ ∋< l > x : A →
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ l ⟩ var x : A.
Proof.
  intros hx hc.
  eapply varty_trans in hx as hx'. 2: eassumption.
  destruct hx' as (A' & hx' & hA).
  eexists _,_. split.
  { econstructor. 2: eauto. apply hc. }
  intuition constructor.
Qed.


    
Lemma tr_ctx_cons Γ Γ' A A' i :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx (Γ ,, (i, A)) (Γ' ,, (i, A')).
Proof.
  intros [hc1 hc2] (? & ? & hs).
  split.
  - econstructor. all: eauto.
  - econstructor. 2: eassumption.
    cbn. intuition auto.
Qed.

Lemma tr_Sort Γ Γ' l :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ Ax (Ax l) ⟩ Sort l : Sort (Ax l) ↦ Sort l : Sort (Ax l).
Proof.
  intros hc.
  split. 2: intuition constructor.
  econstructor. apply hc.
Qed.

Lemma tr_Pi i j Γ' A A' B B' :
  Γ' ⊨⟨ Ax i ⟩ A : Sort i ↦ A' : Sort i →
  Γ',, (i, A') ⊨⟨ Ax j ⟩ B : Sort j ↦ B' : Sort j →
  Γ' ⊨⟨ Ax (Ru i j) ⟩ Pi i j A B : Sort (Ru i j) ↦ Pi i j A' B' : Sort (Ru i j).
Proof.
  intros ihA ihB.
  destruct ihA as (? & ? & ?), ihB as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_Nat Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 1 ⟩ Nat : Sort (ty 0) ↦ Nat : Sort (ty 0).
Proof.
  intro hc.
  split. 2: intuition constructor.
  constructor.
  apply hc.
Qed.

Lemma tr_zero_full Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat ↦ zero : Nat.
Proof.
  intros hc.
  split. 2: intuition constructor.
  constructor. apply hc.
Qed.

Lemma tr_zero Γ Γ' :
  tr_ctx Γ Γ' →
  Γ' ⊨⟨ ty 0 ⟩ zero : Nat.
Proof.
  intros hc.
  eexists _,_. eapply tr_zero_full. eassumption.
Qed.

Lemma tr_succ_full Γ' t t' :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat ↦ t' : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat ↦ succ t' : Nat.
Proof.
  intros iht.
  destruct iht as (? & ? & ?).
  split. 2: intuition (constructor ; eauto).
  constructor. assumption.
Qed.

Lemma tr_succ Γ' t :
  Γ' ⊨⟨ ty 0 ⟩ t : Nat →
  Γ' ⊨⟨ ty 0 ⟩ succ t : Nat.
Proof.
  intros iht.
  eapply keep_head in iht. 2: econstructor.
  destruct iht as (? & hh & iht). inversion hh. subst.
  destruct iht as (? & ?).
  eexists _,_. eapply tr_succ_full. eassumption.
Qed.

Definition tr_subst_data Γ' σ σ' Δ' :=
  Γ' ⊢ps σ' : Δ' ∧ dec_subst σ σ'.

Notation "Γ ⊨s σ : Δ ⇒ σ'" :=
  (tr_subst_data Γ σ σ' Δ)
  (at level 50, σ, Δ at next level).

Definition tr_subst Γ' σ Δ' :=
  ∃ σ', tr_subst_data Γ' σ σ' Δ'.

Notation "Γ ⊨s σ : Δ" :=
  (tr_subst Γ σ Δ)
  (at level 50, σ, Δ at next level).

#[export] Instance dec_subst_morphism :
  Proper ((`=1`) ==> (`=1`) ==> iff) dec_subst.
Proof.
  intros σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  intros x. rewrite <- e, <- e'. apply h.
Qed.

#[export] Instance tr_subst_data_morphism :
  Proper (eq ==> (`=1`) ==> (`=1`) ==> eq ==> iff) tr_subst_data.
Proof.
  intros Γ ? <- σ σ' e θ θ' e' Δ ? <-.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  destruct h. split.
  - rewrite <- e'. assumption.
  - rewrite <- e, <- e'. assumption.
Qed.

#[export] Instance tr_subst_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) tr_subst.
Proof.
  intros Γ ? <- σ σ' e Δ ? <-.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  destruct h as [s h]. exists s.
  rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_tr_subst_data :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    tr_subst_data Γ s1 s3 Δ ↔ tr_subst_data Γ s2 s4 Δ.
Proof.
  intros * h1 h2.
  apply tr_subst_data_morphism. 1,4: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst_data : rasimpl_outermost.

Lemma autosubst_simpl_tr_subst :
  ∀ Γ Δ s1 s2,
    SubstSimplification s1 s2 →
    tr_subst Γ s1 Δ ↔ tr_subst Γ s2 Δ.
Proof.
  intros * h.
  apply tr_subst_morphism. 1,3: eauto.
  apply h.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_tr_subst : rasimpl_outermost.

Lemma tr_subst_scons l Γ' Δ' σ σ' A A' u u' :
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ l ⟩ u : A <[ σ ] ↦ u' : A' <[ σ' ] →
  Γ' ⊨s (u .: σ) : Δ' ,, (l, A') ⇒ (u' .: σ').
Proof.
  intros [hs1 hs2] [hu1 hu2].
  split.
  - apply well_scons_alt. all: eauto.
  - apply dec_subst_scons. all: intuition eauto.
Qed.

Lemma tr_subst_ren Γ Γ' Δ' ρ :
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨s (ρ >> var) : Δ' ⇒ (ρ >> var).
Proof.
  intros hc hr.
  split. 2: apply dec_subst_refl.
  (* 2:{intros. unfold ">>". econstructor. } *)
  apply WellSubst_ren.
  - assumption.
  - apply hc.
Qed.

Lemma tr_subst_one Γ' i A A' u u' :
  Γ' ⊨⟨ i ⟩ u : A ↦ u' : A' →
  Γ' ⊨s u .. : Γ' ,, (i, A') ⇒ (u' ..).
Proof.
  intros hu.
  split.
  - apply subst_one. apply hu.
  - apply dec_subst_one. apply hu.
Qed.

Lemma tr_rename l Γ Γ' Δ' t t' A A' ρ :
  Δ' ⊨⟨ l ⟩ t : A ↦ t' : A' →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ t : ρ ⋅ A ↦ ρ ⋅ t' : ρ ⋅ A'.
Proof.
  intros ht hc hr.
  destruct ht.
  split.
  - eapply typing_conversion_ren. all: eauto. apply hc.
  - intuition eauto using rename_dec.
Qed.

Lemma tr_rename_sort l Γ Γ' Δ' i A A' ρ :
  Δ' ⊨⟨ l ⟩ A : Sort i ↦ A' : Sort i →
  tr_ctx Γ Γ' →
  Γ' ⊢r ρ : Δ' →
  Γ' ⊨⟨ l ⟩ ρ ⋅ A : Sort i ↦ ρ ⋅ A' : Sort i.
Proof.
  intros ht hc hr.
  eapply tr_rename in ht. 2,3: eauto.
  assumption.
Qed.

Lemma tr_substitution i Γ Γ' t t' A A' Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ t <[ σ ] : A <[ σ ] ↦ t' <[ σ' ] : A' <[ σ' ].
Proof.
  intros hc ht hs.
  destruct ht as (? & ? & ?), hs as (? & ?).
  split. 2: intuition eauto using substs_decs.
  eapply typing_conversion_subst.
  - eassumption.
  - apply hc.
  - assumption.
Qed.

Corollary tr_substitution_sort i Γ Γ' A A' l Δ' σ σ' :
  tr_ctx Γ Γ' →
  Δ' ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨s σ : Δ' ⇒ σ' →
  Γ' ⊨⟨ i ⟩ A <[ σ ] : Sort l ↦ A' <[ σ' ] : Sort l.
Proof.
  intros hc ht hs.
  eapply tr_substitution in hs. 2,3: eassumption.
  assumption.
Qed.

Corollary tr_substitution_one i j Γ Γ' t t' u u' A A' B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ t : A ↦ t' : A' →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ t <[ u .. ] : A <[ u .. ] ↦ t' <[ u' .. ] : A' <[ u' .. ].
Proof.
  intros hc ht hu.
  eapply tr_substitution. 1,2: eassumption.
  eapply tr_subst_one. eassumption.
Qed.

Corollary tr_substitution_one_sort i j Γ Γ' A A' u u' l B B' :
  tr_ctx Γ Γ' →
  Γ',, (j,B') ⊨⟨ i ⟩ A : Sort l ↦ A' : Sort l →
  Γ' ⊨⟨ j ⟩ u : B ↦ u' : B' →
  Γ' ⊨⟨ i ⟩ A <[ u .. ] : Sort l ↦ A' <[ u' .. ] : Sort l.
Proof.
  intros hc ht hu.
  eapply tr_substitution_one in hu. 2,3: eassumption.
  assumption.
Qed.

Lemma tr_acc Γ' n A A' R R' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ,, (ty n, A'),, (ty n, S ⋅ A') ⊨⟨ Ax prop ⟩ R : Sort prop ↦ R' : Sort prop →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ Ax prop ⟩ acc (ty n) A R a : Sort prop ↦ acc (ty n) A' R' a' : Sort prop.
Proof.
  intros ihA ihR iha.
  destruct
    ihA as (? & ? & _),
    ihR as (? & ? & _),
    iha as (? & ? & _).
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eauto.
Qed.

Lemma tr_obseq Γ' n A A' a a' b b' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ ty n ⟩ b : A ↦ b' : A' →
  Γ' ⊨⟨ Ax prop ⟩ obseq (ty n) A a b : Sort prop ↦ obseq (ty n) A' a' b' : Sort prop.
Proof.
  intros ihA iha ihb.
  destruct ihA, iha, ihb.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

Lemma tr_obsrefl Γ' n A A' a a' :
  Γ' ⊨⟨ Ax (ty n) ⟩ A : Sort (ty n) ↦ A' : Sort (ty n) →
  Γ' ⊨⟨ ty n ⟩ a : A ↦ a' : A' →
  Γ' ⊨⟨ prop ⟩ obsrefl (ty n) A a : obseq (ty n) A a a ↦ obsrefl (ty n) A' a' : obseq (ty n) A' a' a'.
Proof.
  intros ihA iha.
  destruct ihA, iha.
  split. 2: intuition (constructor ; eauto).
  econstructor. all: eassumption.
Qed.

(* Translation of conversion *)

(* not exactly the same statement as the one written in the paper, however they are logically equivalent *)
Inductive eqtrans Γ' t u A : level -> Prop :=
  | eqtrans_prop : eqtrans Γ' t u A prop
  | eqtrans_ty i t' u' A' e :
    A ⊏ A' ->
    t ⊏ t' ->
    u ⊏ u' ->
    Γ' ⊢p< ty i > t' : A' ->
    Γ' ⊢p< ty i > u' : A' ->
    Γ' ⊢p< prop > e : heq (ty i) A' A' t' u' ->
    eqtrans Γ' t u A (ty i).

Notation "D ⊨⟨ l ⟩ t = u : A" := 
  (eqtrans D t u A l)
  (at level 50, t, u, A at next level).    

Inductive heqtrans Γ' l t u (A B : term) A' B' : Prop :=
  | heqtrans_in e t' u' :
    t ⊏ t' ->
    u ⊏ u' ->
    Γ' ⊢p< l > t' : A' ->
    Γ' ⊢p< l > u' : B' ->
    Γ' ⊢p< prop > e : heq l A' B' t' u' ->
    heqtrans Γ' l t u A B A' B'.

  
Notation "D ⊨⟨ l ⟩ t : A ↦ A' = u : B ↦ B'" := 
  (heqtrans D l t u A B A' B')
  (at level 50, t, A, A', u, B, B' at next level).    


Lemma type_hetero_to_homo' : forall n Γ t u A e,
  Γ ⊢p< ty n > t : A ->
  Γ ⊢p< ty n > u : A ->
  Γ ⊢p< prop > e : heq (ty n) A A t u ->
  exists e', Γ ⊢p< prop > e' : obseq (ty n) A t u.
Proof.
  intros. eapply type_hetero_to_homo in H1; eauto.
Qed.

Lemma tr_eq_ty_geth Γ n t u A A' B B' e:
  A ⊏ A' ->
  B ⊏ B' ->
  Γ ⊢p< Ax (ty n) > A' : Sort (ty n) ->
  Γ ⊢p< Ax (ty n) > B' : Sort (ty n) ->
  Γ ⊢p< prop > e : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A' B' -> 
  Γ ⊨⟨ ty n ⟩ t = u : A ->
  Γ ⊨⟨ ty n ⟩ t : A ↦ A' = u : B ↦ B'.
Proof.
  intros A_dec_A' B_dec_B' A'_Wt B'_Wt A'_eq_B' H.
  dependent destruction H. rename A'0 into A''.
  assert (A'' ~ A') as A''_sim_A' by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in A''_sim_A' as (e' & A''_eq_A'); eauto using validity_ty_ty.
  eapply type_heq_trans in A'_eq_B' as A''_eq_B'. 
  5:eapply A''_eq_A'.
  all: eauto using validity_ty_ty.
  eapply type_hetero_to_homo' in A''_eq_A' as (e1 & A''_eq_A'); 
    eauto using validity_ty_ty.
  eapply type_hetero_to_homo' in A''_eq_B' as (e2 & A''_eq_B'); 
    eauto using validity_ty_ty.
  eapply type_heq_cast in H2 as t'_eq_t''. 
  4:eapply A''_eq_A'. all:eauto using validity_ty_ty.
  eapply type_heq_cast in H3 as u'_eq_u''.
  4:eapply A''_eq_B'. all:eauto using validity_ty_ty.
  eassert (exists e0, Γ ⊢p< prop > e0 : 
    heq (ty n) A' B' (cast (ty n) A'' A' e1 t') (cast (ty n) A'' B' e2 u'))
    as (e'' & t''_eq_u'').
  { eexists. eapply type_heq_trans. 5:eapply u'_eq_u''.
    4:eapply type_heq_trans. 8:eapply H4.
    all:eauto using validity_ty_ty, type_cast, type_heq_sym. }
  econstructor.
  5:eapply t''_eq_u''.
  all:eauto using decoration, type_cast, validity_ty_ty.
Qed.


Lemma tr_eq_ty_sgeth Γ n t u A A':
  A ⊏ A' ->
  Γ ⊢p< Ax (ty n) > A' : Sort (ty n) ->
  Γ ⊨⟨ ty n ⟩ t = u : A ->
  Γ ⊨⟨ ty n ⟩ t : A ↦ A' = u : A ↦ A'.
Proof.
  intros.
  eapply tr_eq_ty_geth; eauto.
  eapply type_heq_refl; eauto using typing, validity_ty_ctx.
Qed.

Lemma tr_tm_get Γ l t A A':
  A ⊏ A' ->
  Γ ⊢p< Ax l > A' : Sort l ->
  Γ ⊨⟨ l ⟩ t : A ->
  exists t',
    t ⊏ t' /\
    Γ ⊢p< l > t' : A'.
Proof.
  intros A_dec_A' A'_Wt t_tr.
  destruct t_tr as (A'' & t' & t'_Wt & t_dec_t' & A_dec_A'').
  assert (A'' ~ A') as A''_sim_A' by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in A''_sim_A' as (e & A''_eq_A'); eauto using validity_ty_ty.
  eapply type_hetero_to_homo' in A''_eq_A' as (e' & A''_eq_A'); 
    eauto using validity_ty_ty.
  eapply type_cast in t'_Wt as t''_Wt; eauto using validity_ty_ty.
  eexists. split. 2:eapply t''_Wt. econstructor; eauto.
Qed.


Lemma tr_eq_prop_geth Γ t u A A' B B' e:
  A ⊏ A' ->
  B ⊏ B' ->
  Γ ⊢p< Ax prop > A' : Sort prop ->
  Γ ⊢p< Ax prop > B' : Sort prop ->
  Γ ⊢p< prop > e : heq (Ax prop) (Sort prop) (Sort prop) A' B' -> 
  Γ ⊨⟨ prop ⟩ t : A ->
  Γ ⊨⟨ prop ⟩ u : B ->
  Γ ⊨⟨ prop ⟩ t : A ↦ A' = u : B ↦ B'.
Proof.
  intros A_dec_A' B_dec_B' A'_Wt B'_Wt A'_eq_B' t_tr u_tr.
  eapply tr_tm_get in t_tr as (t' & t_dec_t' & t'_Wt); eauto.
  eapply tr_tm_get in u_tr as (u' & u_dec_u' & u'_Wt); eauto.
  eapply type_hetero_to_homo' in A'_eq_B' as (e' & A'_eq_B'); eauto.
  econstructor.
  3:eapply t'_Wt. 3:eapply u'_Wt.
  1,2:eauto using decoration.
  eapply type_true_heq; eauto.
Qed.


(* Lemma OLD_tr_eq_prop_geth Γ t u A A' B B' e:
  A ⊏ A' ->
  B ⊏ B' ->
  Γ ⊢p< Ax prop > A' : Sort prop ->
  Γ ⊢p< Ax prop > B' : Sort prop ->
  Γ ⊢p< prop > e : heq (Ax prop) (Sort prop) (Sort prop) A' B' -> 
  Γ ⊨⟨ prop ⟩ t : A ->
  Γ ⊨⟨ prop ⟩ u : A ->
  Γ ⊨⟨ prop ⟩ t : A ↦ A' = u : B ↦ B'.
Proof.
  intros A_dec_A' B_dec_B' A'_Wt B'_Wt A'_eq_B' t_tr u_tr.
  eapply tr_tm_get in t_tr as (t' & t_dec_t' & t'_Wt); eauto.
  eapply tr_tm_get in u_tr as (u' & u_dec_u' & u'_Wt); eauto.
  eapply type_hetero_to_homo' in A'_eq_B' as (e' & A'_eq_B'); eauto.
  eapply type_cast in u'_Wt as u''_Wt; eauto.
  econstructor.
  3:eapply t'_Wt. 3:eapply u''_Wt.
  1,2:eauto using decoration.
  eapply type_true_heq; eauto.
Qed. *)


Lemma decombine_subst_aux Γ i A1 A2 e :
  Γ ⊢p< Ax i > A1 : Sort i ->
  Γ ⊢p< Ax i > A2 : Sort i ->
  Γ ⊢p< prop > e : obseq (Ax i) (Sort i) A1 A2 ->
  Γ ,, (i, A1) ⊢p< i > cast i (S ⋅ A1) (S ⋅ A2) (S ⋅ e) (var 0) : S ⋅ A2.
Proof.
  intros.
  econstructor; eauto. 
  1,2,3:eapply type_ren; eauto using ctx_typing, WellRen_S, validity_ty_ctx.
  econstructor. 2:econstructor. econstructor; eauto using validity_ty_ctx.
Qed.

Lemma cast_subst Γ i A1 A2 e :
  Γ ⊢p< Ax i > A1 : Sort i ->
  Γ ⊢p< Ax i > A2 : Sort i ->
  Γ ⊢p< prop > e : obseq (Ax i) (Sort i) A1 A2 ->
  Γ ,, (i, A1) ⊢ps (cast i (S ⋅ A1) (S ⋅ A2) (S ⋅ e) (var 0).: (S >> var)) : Γ ,, (i, A2).
Proof.
  intros.
  econstructor;ssimpl.
  2:rasimpl ; econstructor.
  2-4:eapply type_ren; eauto using ctx_typing, WellRen_S, validity_ty_ctx.
  2:econstructor. 3:econstructor. 2:eauto using ctx_typing, validity_ty_ctx.
  eapply WellSubst_morphism. 4:eapply WellSubst_weak.
  1:reflexivity.
  3:eapply subst_id. all:eauto using validity_ty_ctx.
  unfold pointwise_relation. intros. destruct a.
  all:reflexivity.
Qed.

Lemma cast_subst2 Γ i j A2 A1 B2 B1 eA eB :
  Γ ,, (i, A2) ⊢p< Ax j > B2 : Sort j ->
  Γ ,, (i, A1) ⊢p< Ax j > B1 : Sort j ->
  
  Γ ⊢p< prop > eA : obseq (Ax i) (Sort i) A2 A1 ->
  let Aeq := heq i ((S >> S) ⋅ A2) ((S >> S) ⋅ A1) (var 1) (var 0) in

  Γ ,, (i, A2) ⊢p< prop > eB : obseq (Ax j) (Sort j) B2 (B1<[cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0).: (S >> var)]) ->

  Γ ,, (i, A2) ,, (j, B2) ⊢ps (cast j (S ⋅ B2) (S ⋅ ((B1<[cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0).: (S >> var)]))) (S ⋅ eB) (var 0) .: 
    (cast i ((S >> S) ⋅ A2) ((S >> S) ⋅ A1) ((S >> S) ⋅ eA) (var 1) .: (S >> S >> var))) :  Γ ,, (i, A1) ,, (j, B1).
Proof.
  intros.
  eapply validity_ty_ctx in H as H'. dependent destruction H'. clear H'.
  eapply validity_ty_ctx in H0 as H0'. dependent destruction H0'. clear H0'.
  econstructor. 
  1:econstructor. all:ssimpl.
  1:replace (S >> (S >> var)) with (var >> ren_term (S >> S)) by (rasimpl; reflexivity).
  1:eapply WellSubst_weak_two; eauto using ctx_typing, validity_ty_ctx, subst_id.
  1:{ eapply meta_conv.
    1:econstructor.
    1-3:eapply type_ren ; eauto using WellRen_S, ctx_typing, validity_ty_ctx, WellRen_weak.
    2:rasimpl;reflexivity.
    econstructor.
    2:eapply varty_meta.
    2:econstructor;econstructor.
    1:eauto using ctx_typing, validity_ty_ctx.
    rasimpl;reflexivity. }
  eapply meta_conv.
  1:econstructor.
  1,3:eapply type_ren ; eauto using WellRen_S, ctx_typing, validity_ty_ctx, WellRen_weak.
  1:rasimpl;f_equal; rasimpl; f_equal; f_equal; f_equal; rasimpl; reflexivity.
  3:rasimpl;reflexivity.
  2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx, ctx_typing.
  eapply subst_ty; eauto using validity_ty_ctx, ctx_typing.
  econstructor.
  all:ssimpl.
  2:{ eapply meta_conv.
    1:econstructor.
    1-3:eapply type_ren ; eauto using WellRen_S, ctx_typing, validity_ty_ctx, WellRen_weak.
    2:rasimpl;reflexivity.
    econstructor.
    2:eapply varty_meta.
    2:econstructor;econstructor.
    1:eauto using ctx_typing, validity_ty_ctx.
    rasimpl;reflexivity. }
  1:replace (S >> (S >> var)) with (var >> ren_term (S >> S)) by (rasimpl; reflexivity).
  1:eapply WellSubst_weak_two; eauto using ctx_typing, validity_ty_ctx, subst_id.
Qed.

Lemma cast_subst_refines t u i A B e : 
  t ⊏ u ->
  t ⊏ u <[ (cast i A B e (var 0)) .: (S >> var)].
Proof.
  intros. 
  replace t with (t <[ (var 0) .: (S >> var)]).
  2:setoid_rewrite subst_id_reduce1; rasimpl; reflexivity.
  eapply substs_decs. 2:eauto.
  unfold dec_subst. intros.
  destruct x.
  - simpl. econstructor. econstructor.
  - simpl. unfold ">>". econstructor.
Qed.

Lemma cast_subst_refines2 t u i A B j C D e' e : 
  t ⊏ u ->
  t ⊏ u <[ (cast i A B e (var 0))  .: ((cast j C D e' (var 1)) .: ((S>>S) >> var))].
Proof.
  intros. 
  replace t with (t <[ (var 0) .: ((var 1) .: ((S >> S) >> var))]).
  2:setoid_rewrite subst_id_reduce2; rasimpl; reflexivity.
  eapply substs_decs. 2:eauto.
  unfold dec_subst. intros.
  destruct x. 2:destruct x.
  - simpl. econstructor. econstructor.
  - simpl. econstructor. econstructor.
  - simpl. unfold ">>". econstructor.
Qed.


Lemma decombine_subst Γ i A1 A2 e :
  Γ ⊢p< Ax i > A1 : Sort i ->
  Γ ⊢p< Ax i > A2 : Sort i ->
  Γ ⊢p< prop > e : obseq (Ax i) (Sort i) A2 A1 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in    
  exists e',
  Γ ,, (i, A2) ⊢ps (e' .: ((var 0) .: ((cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ e) (var 0)) .: (S >> var)))) : Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq).
Proof.
  intros.
  eapply decombine_subst_aux in H1 as h1; eauto.
  eexists. 
  econstructor. 1:econstructor.
  2,3:unfold ">>"; simpl; rasimpl.
  2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx, ctx_typing.
  2:unfold Aeq. 2:rewrite heq_subst. 2:rasimpl.
  2:eapply type_heq_sym; eauto.
  2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx, ctx_typing.
  2:eapply type_heq_cast; eauto using type_ren, ctx_typing, WellRen_S, validity_ty_ctx.
  2:econstructor. 3:econstructor. 2:eauto using validity_ty_ctx, ctx_typing.
  ssimpl.
  econstructor. 
  2:ssimpl. 2:renamify; eauto.
  eapply WellSubst_morphism.
  4:eapply WellSubst_weak.
  4:eapply subst_id.
  3:{ unfold pointwise_relation. intros.
      destruct a; unfold ">>". 1:simpl;reflexivity.
      simpl. reflexivity. }
  all:eauto using validity_ty_ctx.
Qed. 

Lemma cast_subst2_aux  Γ i j A2 A1 B2 B1 eA e :
  Γ ,, (i, A2) ⊢p< Ax j > B2 : Sort j ->
  Γ ,, (i, A1) ⊢p< Ax j > B1 : Sort j ->
  Γ ⊢p< prop > eA : obseq (Ax i) (Sort i) A2 A1 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (i, A1) ,, (i, S ⋅ A2),, (prop, Aeq) ⊢p< prop > e : heq (Ax j) (Sort j) (Sort j) ((S >> S) ⋅ B1) ((up_ren S >> S) ⋅ B2) ->
  exists eB,
    Γ ,, (i, A2) ⊢p< prop > eB : obseq (Ax j) (Sort j) B2 (B1<[cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0).: (S >> var)]).
Proof.
  intros.
  eapply validity_ty_ctx in H as H'. dependent destruction H'. clear H'.
  eapply validity_ty_ctx in H0 as H0'. dependent destruction H0'. clear H0'.
  eapply decombine_subst in H1 as H1'; eauto. destruct H1'.
  eapply type_hetero_to_homo' in H2.
  2,3:eapply type_ren; eauto using ctx_extend_Wt, validity_ty_ctx, WellRen_S, WellRen_weak, WellRen_up.
  destruct H2.
  eapply type_obseq_sym in H2.
  econstructor.
  eapply subst_ty.
  2:eapply H5.
  2:eauto.
  1:eauto using validity_ty_ctx, ctx_typing.
  rasimpl. setoid_rewrite subst_id_reduce1. rasimpl; reflexivity.
Qed.

Lemma decombine_subst2 Γ i j A2 A1 B2 B1 eA eB :
  Γ ,, (i, A2) ⊢p< Ax j > B2 : Sort j ->
  Γ ,, (i, A1) ⊢p< Ax j > B1 : Sort j ->
  
  Γ ⊢p< prop > eA : obseq (Ax i) (Sort i) A2 A1 ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  let Beq := heq j ((((S >> S) >> S) >> S) ⋅ B1) ((((up_ren S >> S) >> S) >> S) ⋅ B2) (var 1) (var 0) in

  Γ ,, (i, A2) ⊢p< prop > eB : obseq (Ax j) (Sort j) B2 (B1<[cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0).: (S >> var)])  ->

  exists eA' eB',
  Γ ,, (i, A2) ,, (j, B2) ⊢ps  (eB' .: ( (var 0) .: (cast j (S ⋅ B2) (S ⋅ ((B1<[cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0).: (S >> var)]))) (S ⋅ eB) (var 0)  .:
    ( eA' .: ((var 1) .:  (cast i ((S >> S) ⋅ A2) ((S >> S) ⋅ A1) ((S >> S) ⋅ eA) (var 1)  .: (S >> S >> var))))))) :  
    (((((Γ,, (i, A1)),, (i, S ⋅ A2)),, (prop, Aeq)),, (j, (S >> S) ⋅ B1)),, (j, ((up_ren S >> S) >> S) ⋅ B2)),, (prop, Beq).
Proof.
  intros. eapply type_obseq_sym in H1 as H1'. eapply type_obseq_sym in H2 as H2'.
  eapply validity_ty_ctx in H as H'. dependent destruction H'. clear H'.
  eapply validity_ty_ctx in H0 as H0'. dependent destruction H0'. clear H0'.

  eapply decombine_subst_aux in H1 as h1; eauto.
  eassert ((Γ,, (i, A2)),, (j, B2) ⊢p< j > cast j (S ⋅ B2) (S ⋅ B1 <[ cast i (S ⋅ A2) (S ⋅ A1) (S ⋅ eA) (var 0) .: S >> var]) (S ⋅ eB) (var 0) : _).
  { econstructor.
    1-3:eapply type_ren; eauto using WellRen_S, ctx_typing, validity_ty_ctx.
    1:eapply subst_ty; eauto using validity_ty_ctx.
    2:reflexivity.
    1:eapply cast_subst; eauto.
    econstructor. 2:econstructor. eauto using ctx_typing, validity_ty_ctx. }
  
  assert ((Γ,, (i, A2)),, (j, B2) ⊢p< i > cast i ((S >> S) ⋅ A2) ((S >> S) ⋅ A1) ((S >> S) ⋅ eA) (var 1) : A1 <[ λ x : nat, var (S (S x))]).
  { eapply meta_conv.
    1:eapply meta_tm_conv.
    1:eapply type_ren.
    1:eapply h1. 2:eapply WellRen_S.
    all:eauto using validity_ty_ctx, ctx_typing.
    all:rasimpl. 1:reflexivity.
    1:substify. ssimpl. unfold ">>". reflexivity. }

  assert ((Γ,, (i, A2)),, (j, B2) ⊢p< i > var 1 : A2 <[ λ x : nat, var (S (S x))]).
  { econstructor; eauto using ctx_typing, validity_ty_ctx.
    eapply varty_meta.
    1:eauto using varty.
    substify. ssimpl. unfold ">>". reflexivity. }

  assert ((Γ,, (i, A2)),, (j, B2) ⊢p< j > 
    cast j (S ⋅ B2) (B1 <[ cast i ((S ⋅ A2) <[ S >> var]) ((S ⋅ A1) <[ S >> var]) ((S ⋅ eA) <[ S >> var]) ((S >> var) 0) .: (S >> S) >> var]) (S ⋅ eB) (var 0)
    : B1 <[ cast i ((λ x : nat, S (S x)) ⋅ A2) ((λ x : nat, S (S x)) ⋅ A1) ((λ x : nat, S (S x)) ⋅ eA) (var 1) .: λ x : nat, var (S (S x))]).
  { 
    eapply meta_conv.
    1:econstructor.
    1,3:eapply type_ren; eauto using validity_ty_ctx, ctx_typing, WellRen_weak, WellRen_S.
    1:rasimpl; reflexivity.
    2:econstructor; eauto using varty, ctx_typing, validity_ty_ctx.
    2:rasimpl; f_equal; f_equal; f_equal;  substify; ssimpl; unfold ">>"; reflexivity.
    eapply subst_ty; eauto using validity_ty_ctx, ctx_typing.
    econstructor; ssimpl.
    1:change (S >> (S >> var)) with (var >> ren_term (S >> S)).
    1:eapply WellSubst_weak_two; eauto using validity_ty_ctx, ctx_typing, subst_id.
    eapply meta_conv. 1:eapply meta_tm_conv. 1:eapply H6.
    1:f_equal; f_equal; f_equal. all:  substify; ssimpl; unfold ">>"; reflexivity. }



  eexists _,_.

  econstructor.  1:econstructor. 1:econstructor. 1:econstructor. 1:econstructor. 1:econstructor. 
  2-7:unfold ">>"; simpl; rasimpl.
  1:shelve.
  1,2:eassumption.
  * unfold Aeq. rewrite heq_subst.
    rasimpl. eapply type_heq_sym; eauto.
    eapply meta_conv.
    1:eapply type_heq_cast.
    1,2:eapply type_ren.
    1:eapply H3. 4:eapply H4.
    all:eauto using ctx_typing, validity_ty_ctx, WellRen_weak, WellRen_S.
    2:eapply type_var.
    3:eapply varty_meta. 3:eapply vartyS, vartyO.
    2:eauto using validity_ty_ctx, ctx_typing.
    2:rasimpl;reflexivity.
    2:f_equal; substify; ssimpl; unfold ">>"; reflexivity.
    eapply type_ren; eauto using validity_ty_ctx, ctx_typing, WellRen_weak, WellRen_S. 
  * rasimpl. eassumption.
  * rasimpl. econstructor; eauto using validity_ty_ctx, ctx_typing.
    eapply varty_meta. 1:econstructor.
    substify; ssimpl; unfold ">>". eapply subst_term_morphism; eauto.
    unfold pointwise_relation; intro x; destruct x; reflexivity.
  * unfold Beq. rewrite heq_subst. rasimpl. 
    eapply type_heq_sym. 2:rasimpl; eassumption.
    1:{econstructor; eauto using ctx_typing, validity_ty_ctx; eapply varty_meta. 1:econstructor.
      substify; ssimpl; unfold ">>"; eapply subst_term_morphism; eauto.
      unfold pointwise_relation; intro x; destruct x; reflexivity. }
    eapply meta_conv.
    1:eapply type_heq_cast.
    3:eapply type_ren.
    3:eapply H2. 4:eapply WellRen_S.
    4:simpl; reflexivity.
    4:eapply type_var;eauto using varty, ctx_typing, validity_ty_ctx.
    3:eauto using ctx_typing, validity_ty_ctx.
    3:rasimpl; f_equal; f_equal; f_equal; substify; ssimpl; unfold ">>".
    4:reflexivity. 3:eapply subst_term_morphism; eauto.
    3:unfold pointwise_relation; intro x; destruct x; reflexivity.
    all:eapply type_inv in H5; dependent destruction H5; eauto. 
  Unshelve. 
  ssimpl.
  change (S >> (S >> var)) with (var >> ren_term (S >> S)).
  eapply WellSubst_weak_two; eauto using validity_ty_ctx, ctx_typing, subst_id. 
Qed.

Lemma renproj1 Γ A1 A2 Aeq i : 
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq) ⊢r (S >> S) : Γ ,, (i, A1).
Proof.
  eauto using WellRen_weak, WellRen_S.
Qed.

Lemma renproj2 Γ A1 A2 Aeq i : 
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq) ⊢r (up_ren S >> S) : Γ ,, (i, A2).
Proof.
  eapply WellRen_weak.
  eapply WellRen_up.
  all:eauto using WellRen_S.
Qed.


Lemma type_heq_trans' : forall Γ l A B C c b a e1 e2,
  Γ ⊢p< l > a : A ->
  Γ ⊢p< l > b : B ->
  Γ ⊢p< l > c : C ->
  Γ ⊢p< prop > e1 : heq l A B a b →
  Γ ⊢p< prop > e2 : heq l B C b c → 
  exists e, Γ ⊢p< prop > e : heq l A C a c.  
Proof.
  intros. eexists. eapply type_heq_trans. 4,5:eassumption. all:eauto.
Qed.

Lemma tr_eq_ty_cons_geth Γ' n i A1 A2 A1' A2' B1 B2 B1' B2' t u  e e_ :
  A1 ⊏ A1' ->
  B1 ⊏ B1' ->
  A2 ⊏ A2' ->
  B2 ⊏ B2' ->
  let Aeq := heq i ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0) in
  Γ' ,, (i, A1') ⊢p< Ax (ty n) > B1' : Sort (ty n) ->
  Γ' ,, (i, A2') ⊢p< Ax (ty n) > B2' : Sort (ty n) ->
  Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) ⊢p< prop > e : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) ((S >> S) ⋅ B1') ((up_ren S >> S) ⋅ B2') ->
  Γ' ⊢p< prop > e_ : heq (Ax i) (Sort i) (Sort i) A1' A2' ->
  Γ' ,, (i, A1') ⊨⟨ ty n ⟩ t = u : B1 ->
  exists t' u',
    t ⊏ t' /\
    u ⊏ u' /\
    Γ' ,, (i, A1') ⊢p< ty n > t' : B1' /\
    Γ' ,, (i, A2') ⊢p< ty n > u' : B2' /\
    exists e',
      Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) ⊢p< prop > e' : heq (ty n) ((S >> S) ⋅ B1') ((up_ren S >> S) ⋅ B2')  
        ((S >> S) ⋅ t') ((up_ren S >> S) ⋅ u').
Proof.
  intros.  rename H6 into A1'_heq_A2'.

  assert (Γ' ⊢p< Ax i > A1' : Sort i) as A1'_Wt by 
    (eapply validity_ty_ctx in H3; dependent destruction H3; eauto).
  assert (Γ' ⊢p< Ax i > A2' : Sort i) as A2'_Wt by
    (eapply validity_ty_ctx in H4; dependent destruction H4; eauto).

  assert (exists e_', Γ' ⊢p< prop > e_' : obseq (Ax i) (Sort i) A2' A1') as A2'_eq_A1'
  by eauto using type_hetero_to_homo, type_heq_sym. 
  destruct A2'_eq_A1' as (e_' & A2'_eq_A1').

  dependent destruction H7.  rename H11 into t'_heq_u'.
  rename A' into B1''. rename H9 into t'_Wt. rename H10 into u'_Wt.
  assert (B1'' ~ B1') as B1''_sim_B1' by eauto using dec_to_sim, sim_sym, sim_trans. 
  eapply sim_heq_same_ctx in B1''_sim_B1' as (e' & B1''_heq_B1'); 
    eauto using validity_ty_ty.

  eapply type_hetero_to_homo' in B1''_heq_B1' as B1''_eq_B1'; 
    eauto using validity_ty_ty.

  destruct B1''_eq_B1' as (e'' & B1''_eq_B1').
  eapply type_cast in t'_Wt as t''_Wt; eauto using validity_ty_ty.

  eapply type_heq_cast in t'_Wt as t'_heq_t''; eauto using validity_ty_ty.

  eapply type_ren in B1''_heq_B1'; eauto using renproj1. 2:eauto using validity_ty_ctx.
  rewrite heq_ren in B1''_heq_B1'. simpl in B1''_heq_B1'.
  eapply type_heq_trans in H5 as B1''_heq_B2'; eauto.
  2,3,4:eauto using type_ren, validity_ty_ctx, validity_ty_ty, renproj1, renproj2.
 

  eapply subst_ty in u'_Wt as u''_Wt. 3:eapply cast_subst. 5:eapply A2'_eq_A1'.
  all:eauto using ctx_typing, validity_ty_ctx, validity_ty_ty.


  eapply decombine_subst in A2'_eq_A1' as temp ; eauto. 
  destruct temp as (e''' & temp).
  eapply subst_ty in B1''_heq_B2' as B1''cast_heq_B2'. 3:eapply temp. 
  all :eauto using ctx_typing, validity_ty_ctx.

  rewrite heq_subst in B1''cast_heq_B2'. rasimpl in B1''cast_heq_B2'.
  setoid_rewrite subst_id_reduce1 in B1''cast_heq_B2'. rasimpl in B1''cast_heq_B2'.

  eapply type_hetero_to_homo' in B1''cast_heq_B2' as temp'; 
    eauto using subst_ty, cast_subst, validity_ty_ctx, validity_ty_ty, ctx_typing.

  destruct temp' as (e'''' & B1''cast_eq_B2').

  eapply type_cast in u''_Wt as u'''_Wt; 
    eauto using subst_ty, cast_subst, validity_ty_ctx, validity_ty_ty, ctx_typing.

  eapply type_heq_cast in u''_Wt as u''_heq_u'''; 
    eauto using subst_ty, cast_subst, validity_ty_ctx, validity_ty_ty, ctx_typing.

  eapply type_ren in u''_heq_u'''. 3:eapply renproj2. all:eauto using validity_ty_ctx.
  rewrite heq_ren in u''_heq_u'''.

  eassert (u' ~ u' <[ (cast _ _ _ _ (var 0)).: S >> var]) as u'_sim_u''
    by eauto 10 using dec_to_sim, cast_subst_refines, sim_sym, sim_trans.
  eapply sim_heq_same_ctx_cons in u'_sim_u'' as (e''''' & u'_heq_u''); eauto.

  eapply type_heq_trans' in u''_heq_u''' as temp_;
    eauto using subst_ty, cast_subst, validity_ty_ctx, validity_ty_ty, ctx_typing.
  2-4:eapply type_ren;eauto using renproj1, renproj2, validity_ty_ctx.
  destruct temp_ as (e___ & u'_heq_u''').

  eapply type_heq_sym in t'_heq_t'' as t''_heq_t'; eauto.
  eapply type_heq_trans' in t'_heq_u' as _temp; eauto.
  destruct _temp as (_e & t''_heq_u').
  eapply type_ren in t''_heq_u'; eauto using renproj1. 2:eauto using validity_ty_ctx.

  rewrite heq_ren in t''_heq_u'.
  eapply type_heq_trans' in u'_heq_u''' as _temp. 5:eapply t''_heq_u'.
  2-4:eapply type_ren;eauto using renproj1, renproj2, validity_ty_ctx.
  destruct _temp as (__e & t''_heq_u''').
  
  eexists. eexists. split. 2:split. 3:split. 4:split.
  3:eapply t''_Wt. 3:eapply u'''_Wt. 1,2:econstructor; eauto.
  1:eapply cast_subst_refines; eauto.
  eexists. eapply t''_heq_u'''.
Qed.



Lemma tr_eq_ty_cons_geth_sort Γ' l i A1 A2 A1' A2'  t u  e :
  A1 ⊏ A1' ->
  A2 ⊏ A2' ->
  let Aeq := heq i ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0) in
  Γ' ⊢p< Ax i > A1' : Sort i ->
  Γ' ⊢p< Ax i > A2' : Sort i ->
  Γ' ⊢p< prop > e : heq (Ax i) (Sort i) (Sort i) A1' A2' ->
  Γ' ,, (i, A1') ⊨⟨ Ax l ⟩ t = u : Sort l ->
  exists t' u',
    t ⊏ t' /\
    u ⊏ u' /\
    Γ' ,, (i, A1') ⊢p< Ax l > t' : Sort l /\
    Γ' ,, (i, A2') ⊢p< Ax l > u' : Sort l /\
    exists e',
      Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) ⊢p< prop > e' : heq (Ax l) (Sort l) (Sort l) ((S >> S) ⋅ t') ((up_ren S >> S) ⋅ u').
Proof.
  intros.
  eapply tr_eq_ty_cons_geth; eauto.
  1,2:econstructor.
  1,2:econstructor; eauto using ctx_typing, validity_ty_ctx.
  rasimpl. eapply type_heq_refl.
  all:econstructor; eapply ctx_extend_Wt; eauto using validity_ty_ctx.
Qed.


Lemma renproj1' Γ A1 A2 Aeq B1 B2 Beq j i : 
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq) ,, (j, (S >> S) ⋅ B1) ,, (j, (up_ren S >> S >> S) ⋅ B2) ,, (prop, Beq) 
    ⊢r (up_ren (S >> S) >> S >> S) : Γ ,, (i, A1) ,, (j, B1).
Proof.
  eauto 8 using WellRen_weak, WellRen_S, WellRen_up.
Qed.

Lemma renproj2' Γ A1 A2 Aeq B1 B2 Beq j i :
  Γ ,, (i, A1) ,, (i, S ⋅ A2) ,, (prop, Aeq) ,, (j, (S >> S) ⋅ B1) ,, (j, (up_ren S >> S >> S) ⋅ B2) ,, (prop, Beq) 
    ⊢r (up_ren ((up_ren S >> S) >> S) >> S) : Γ ,, (i, A2) ,, (j, B2).
Proof.
  eauto 8 using WellRen_weak, WellRen_S, WellRen_up.
Qed.


Lemma tr_eq_ty_cons2_geth Γ' n i j A1 A2 A1' A2' B1 B2 B1' B2' C1 C2 C1' C2' t u eA eB eC :
  A1 ⊏ A1' ->
  A2 ⊏ A2' ->
  B1 ⊏ B1' ->
  B2 ⊏ B2' ->
  C1 ⊏ C1' ->
  C2 ⊏ C2' ->

  Γ' ,, (i, A1') ,, (j, B1') ⊢p< Ax (ty n) > C1' : Sort (ty n) ->
  Γ' ,, (i, A2') ,, (j, B2') ⊢p< Ax (ty n) > C2' : Sort (ty n) ->

  Γ' ⊢p< prop > eA : heq (Ax i) (Sort i) (Sort i) A1' A2' ->

  let Aeq := heq i ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0) in
  Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) ⊢p< prop > eB : heq (Ax j) (Sort j) (Sort j) ((S >> S) ⋅ B1') ((up_ren S >> S) ⋅ B2') ->

  let Beq := heq j ((S >> S >> S >> S) ⋅ B1') ((up_ren S >> S >> S >> S) ⋅ B2') (var 1) (var 0) in
  Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) 
    ,, (j, (S >> S) ⋅ B1') ,, (j,  (up_ren S >> S >> S) ⋅ B2') ,, (prop, Beq)
    ⊢p< prop > eC : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) ((up_ren (S >> S) >> S >> S) ⋅ C1') ((up_ren (up_ren S >> S >> S) >> S) ⋅ C2') ->
  
  Γ' ,, (i, A1') ,, (j, B1') ⊨⟨ ty n ⟩ t = u : C1 ->
  exists t' u',
    t ⊏ t' /\
    u ⊏ u' /\
    Γ' ,, (i, A1') ,, (j, B1') ⊢p< ty n > t' : C1' /\
    Γ' ,, (i, A2') ,, (j, B2') ⊢p< ty n > u' : C2' /\
    exists e',
    Γ' ,, (i, A1') ,, (i, S ⋅ A2'),, (prop, Aeq) 
      ,, (j, (S >> S) ⋅ B1') ,, (j,  (up_ren S >> S >> S) ⋅ B2') ,, (prop, Beq)
      ⊢p< prop > e' : heq (ty n) ((up_ren (S >> S) >> S >> S) ⋅ C1') ((up_ren (up_ren S >> S >> S) >> S) ⋅ C2') 
        ((up_ren (S >> S) >> S >> S) ⋅ t') ((up_ren (up_ren S >> S >> S) >> S) ⋅ u').
Proof. 
  intros A1_dec_A1' A2_dec_A2' B1_dec_B1' B2_dec_B2' C1_dec_C1' C2_dec_C2' C1'Wt C2'Wt A1'_heq_A2' * B1'_heq_B2' * C1'_heq_C2' h.
  dependent destruction h. rename A' into C1''.
  rename H2 into t'Wt. rename H3 into u'Wt. rename H4 into t'_heq_u'.
  eapply validity_ty_ctx in C1'Wt as temp'. dependent destruction temp'. rename H2 into B1'Wt. dependent destruction temp'. rename H2 into A1'Wt. clear temp'.
  eapply validity_ty_ctx in C2'Wt as temp'. dependent destruction temp'. rename H2 into B2'Wt. dependent destruction temp'. rename H2 into A2'Wt. clear temp'.

  eapply type_heq_sym in A1'_heq_A2' as temp; eauto. eapply type_hetero_to_homo' in temp; eauto. destruct temp as (? & A2'_eq_A1').

  assert (C1'' ~ C1') as temp by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in temp as (? & C1''_heq_C1'); eauto using validity_ty_ty.
  eapply type_hetero_to_homo' in C1''_heq_C1' as temp; eauto using validity_ty_ty. destruct temp as (? & C1''_eq_C1').
  pose (t'' := cast (ty n) C1'' C1' x1 t'). 
  eapply type_cast in t'Wt as t''Wt; eauto using validity_ty_ty.
  eapply type_heq_cast in t'Wt as t'_heq_t''; eauto using validity_ty_ty.
  fold t'' in t''Wt, t'_heq_t''. 

  eapply cast_subst2_aux in B1'_heq_B2' as temp; eauto. destruct temp as (? & B2'_eq_B1'cast).

  eapply cast_subst2 in B2'_eq_B1'cast as ΓA2B2_to_ΓA1B1; eauto.

  eapply subst_ty in u'Wt as u''Wt. 3:eapply ΓA2B2_to_ΓA1B1.
  all:eauto using ctx_typing, validity_ty_ctx.
  pose (u'' := u' <[ cast j (S ⋅ B2') (S ⋅ B1' <[ cast i (S ⋅ A2') (S ⋅ A1') (S ⋅ x) (var 0) .: S >> var]) (S ⋅ x2) (var 0) .: 
    (cast i ((S >> S) ⋅ A2') ((S >> S) ⋅ A1') ((S >> S) ⋅ x) (var 1) .: (S >> S) >> var)]).
  fold u'' in u''Wt.
  pose (C1''' := C1'' <[ cast j (S ⋅ B2') (S ⋅ B1' <[ cast i (S ⋅ A2') (S ⋅ A1') (S ⋅ x) (var 0) .: S >> var]) (S ⋅ x2) (var 0) .: 
    (cast i ((S >> S) ⋅ A2') ((S >> S) ⋅ A1') ((S >> S) ⋅ x) (var 1) .: (S >> S) >> var)]).
  fold C1''' in u''Wt.
  assert (u' ~ u'') as temp
    by (unfold u''; eauto 6 using dec_to_sim, cast_subst_refines2, sim_sym, sim_trans).

  eapply sim_heq_same_ctx_cons2 in temp as (? & u'_heq_u''); eauto.

  eapply validity_ty_ty in u''Wt as C1'''Wt.

  eapply decombine_subst2 in B2'_eq_B1'cast as decombine; eauto.
  destruct decombine as (? & ? & decombine).

  eapply type_obseq_sym in C1''_eq_C1' as C1'_eq_C1''.
  eapply type_ren in C1'_eq_C1''.
  2:{ eapply validity_ty_ctx in C1'_heq_C2'. eapply C1'_heq_C2'. }
  2:eauto using WellRen_weak, WellRen_up, WellRen_S.
  2:eauto.

  eapply subst_ty in C1'_heq_C2'. 3:unfold Beq, Aeq;rasimpl;rasimpl in decombine; eapply decombine.
  all:eauto using validity_ty_ctx, ctx_typing.
  rewrite heq_subst in C1'_heq_C2'; rasimpl in C1'_heq_C2'; setoid_rewrite subst_id_reduce2 in C1'_heq_C2'; rasimpl in C1'_heq_C2'.
  rename C1'_heq_C2' into C1'''_heq_C2'.

  eapply subst_ty in C1''_heq_C1'.  3:eapply ΓA2B2_to_ΓA1B1.
  all:eauto using validity_ty_ctx.
  rewrite heq_subst in C1''_heq_C1'; rasimpl in C1''_heq_C1'. 
  eapply type_heq_trans' in C1'''_heq_C2'. 
  5:eapply meta_conv. 5:eapply C1''_heq_C1'.
  5:f_equal; rasimpl; f_equal; f_equal; f_equal; rasimpl; reflexivity.
  2,3:eapply subst_ty; eauto using validity_ty_ty.
  4:rasimpl; rasimpl in ΓA2B2_to_ΓA1B1; eapply ΓA2B2_to_ΓA1B1.
  2-4:eauto using validity_ty_ctx, ctx_typing.

  destruct C1'''_heq_C2' as (? & C1''cast_heq_C2'). 

  eapply type_hetero_to_homo' in C1''cast_heq_C2' as temp; eauto.
  destruct temp as (? & C1''cast_eq_C2').

  eapply type_cast in u''Wt as u'''Wt. 4:eapply C1''cast_eq_C2'.
  all:eauto.

  eapply type_heq_cast in u''Wt as u''_heq_u'''.  4:eapply C1''cast_eq_C2'.
  all:eauto.

  pose (u''' := cast (ty n) C1''' C2' x7 u'').
  fold u''' in u''_heq_u''', u'''Wt.


  exists t''. exists u'''.
  split. 2:split. 3:split. 4:split.
  all:eauto.
  1,2:unfold t'', u''', u''; eauto using decoration, cast_subst_refines2.

  eapply type_ren in u''_heq_u'''. 3:eapply renproj2'. 
  2,3:eauto using validity_ty_ctx.
  rewrite heq_ren in u''_heq_u'''.

  eapply type_ren in u'''Wt. 3:eapply renproj2'. 
  2,3:eauto using validity_ty_ctx.

  eapply type_ren in u''Wt. 3:eapply renproj2'. 
  2,3:eauto using validity_ty_ctx.

  eapply type_ren in u'Wt. 3:eapply renproj1'. 
  2,3:eauto using validity_ty_ctx.


  eapply type_ren in t'Wt. 3:eapply renproj1'. 
  2,3:eauto using validity_ty_ctx.

  eapply type_ren in t''Wt. 3:eapply renproj1'. 
  2,3:eauto using validity_ty_ctx.

  eapply type_ren in t'_heq_t''. 3:eapply renproj1'. 
  2,3:eauto using validity_ty_ctx.

  eapply type_ren in t'_heq_u'. 3:eapply renproj1'. 
  2,3:eauto using validity_ty_ctx.

  rewrite heq_ren in t'_heq_t'', t'_heq_u'.

  eapply type_heq_sym in t'_heq_t'' as t''_heq_t'; eauto.

  eapply type_heq_trans in t'_heq_u' as t''_heq_u'; eauto.
  eapply type_heq_trans in u'_heq_u'' as t''_heq_u''; eauto.
  eapply type_heq_trans in u''_heq_u''' as t''_heq_u'''; eauto.
Qed.


Lemma tr_eq_conclude Γ' e l A A' B B' t t' u u' :
  t ⊏ t' ->
  u ⊏ u' ->
  A ⊏ A' ->
  B ⊏ B' ->
  Γ' ⊢p< l > t' : A' ->
  Γ' ⊢p< l > u' : B' ->
  Γ' ⊢p< prop > e : heq l A' B' t' u' ->
  Γ' ⊨⟨ l ⟩ t = u : A.
Proof.
  intros. 
  destruct l. 2:eauto using eqtrans.
  assert (exists e', Γ' ⊢p< prop > e' : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) A' B') by eauto using type_hetero_to_type, validity_ty_ty.
  destruct H6.
  eapply type_hetero_to_homo' in H6; eauto using validity_ty_ty.
  destruct H6.
  eapply type_obseq_sym in H6.
  eapply type_cast in H4 as H4';eauto. all:eauto using validity_ty_ty.
  econstructor.
  4:eapply H3. 4:eapply H4'.
  all:eauto using decoration.
  eapply type_heq_trans.
  4:eapply H5. 4:eapply type_heq_cast.
  all:eauto using validity_ty_ty.
Qed.

Lemma tr_eq_conclude_by_refl Γ' l A A' t t' u u' :
  t ⊏ t' ->
  u ⊏ u' ->
  A ⊏ A' ->
  Γ' ⊢p< l > t' ≡ u' : A' ->
  Γ' ⊨⟨ l ⟩ t = u : A.
Proof.
  intros.
  eapply tr_eq_conclude; eauto using validity_conv_left, validity_conv_right.
  eapply type_conv.
  1:eapply type_heq_refl.
  3:eapply conv_heq.
  6:eassumption.
  all:eauto using validity_conv_left, validity_ty_ty, conv_refl.
Qed. 

Lemma tr_ctx_cons' Γ Γ' A A' l : 
  tr_ctx Γ Γ' ->
  A ⊏ A' ->
  Γ' ⊢p< Ax l > A' : Sort l ->
  tr_ctx (Γ ,, (l, A)) (Γ' ,, (l, A')).
Proof.
  intros.
  econstructor.
  1:econstructor; eauto using validity_ty_ctx.
  econstructor; eauto.
  eapply H.
Qed.


Lemma tr_conv Γ' l t A B : 
  Γ' ⊨⟨ l ⟩ t : A ->
  Γ' ⊨⟨ Ax l ⟩ A = B : Sort l ->
  Γ' ⊨⟨ l ⟩ t : B.
Proof.
  intros.
  destruct H. destruct H. destruct H. destruct H1. rename x0 into t'. rename x into A'.
  eapply tr_eq_ty_sgeth in H0. 2:econstructor. 2:eauto using typing, validity_ty_ctx.
  dependent destruction H0. rename t'0 into A''. rename u' into B'.

  assert (A' ~ A'') by eauto using dec_to_sim, sim_sym, sim_trans.
  eapply sim_heq_same_ctx in H7; eauto using validity_ty_ty.
  destruct H7. eapply type_heq_trans in H6. 5:eassumption. 
  all: eauto using validity_ty_ty.
  eapply type_hetero_to_homo' in H6; eauto using validity_ty_ty.
  destruct H6.
  eapply type_cast in H; eauto using validity_ty_ty.
  eexists. eexists. eexists.
  2:split. 1:eapply H. all:eauto using decoration.
Qed.

Lemma typing_conversion_trans :
  (∀ Γ l t A,
    Γ ⊢d< l > t : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ' ⊨⟨ l ⟩ t : A
  ) ∧
  (∀ Γ l u v A,
    Γ ⊢d< l > u ≡ v : A →
    ∀ Γ',
      tr_ctx Γ Γ' →
      Γ' ⊨⟨ l ⟩ u = v : A
  ).
Proof.
  apply Typing.typing_mutind.

  (* solves SProp equality cases *)
  all : try solve [ intros; eapply eqtrans_prop ].

  (* Typing rules *)

  - intros * ? hx ? hc.
    eapply tr_var. all: eassumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Sort. eassumption.
  - intros * ? e ? ih ? hc.
    rewrite <- assm_sig_ty in t; eauto.
    assert (tr_ctx ∙ ∙) by (econstructor; econstructor).

    eapply ih in H. eapply tr_tm_get in H; eauto using typing, decoration, ctx_typing.
    destruct H as (A' & ? & ?).

    eexists _, (assm _). split.
    { econstructor. 2,3: eassumption. apply hc. }
    intuition eauto using decoration, dec_refl.
  - intros * ? ihA ? ihB ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    eexists _,_. eapply tr_Pi. all: eassumption.
  - intros * ? ihA ? ihB ? iht ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    specialize iht with (1 := hca).
    eapply change_type in iht. 2: eassumption.
    destruct iht as (t' & iht).
    destruct ihA as (? & ? & _), ihB as (? & ? & _), iht as (? & ? & _).
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihB ? iht ? ihu ? hc.
    specialize ihA with (1 := hc).
    eapply keep_sort in ihA. destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca).
    eapply keep_sort in ihB. destruct ihB as (B' & ihB).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Pi. all: eassumption. }
    destruct iht as (t' & iht).
    specialize ihu with (1 := hc).
    eapply change_type in ihu. 2: eassumption.
    destruct ihu as (u' & ihu).
    destruct
      ihA as (? & ? & _),
      ihB as (? & ? & _),
      iht as (? & ? & _),
      ihu as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ?? hc.
    eexists _,_. eapply tr_Nat. eassumption.
  - intros * ?? hc. eapply tr_zero. eassumption.
  - intros * ? iht ? hc.
    specialize iht with (1 := hc).
    eapply tr_succ. assumption.
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _),
      iht as (? & ? & _).
    eexists _,_. split. 2: split. 2: constructor ; eauto.
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: assumption.
  - intros * ? ihA ? ihR ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct ihR as [R' ihR], iha as [a' iha].
    eexists _,_.
    eapply tr_acc. all: eassumption.
  - intros * ? ihA ? ihR ? iha. cbn zeta. intros ? ihp ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eapply tr_ctx_cons in hca as hcar.
    2:{
      eapply tr_substitution_sort. 1,2: eauto.
      eapply tr_subst_scons with (A := S ⋅ A).
      1: eapply tr_subst_scons with (A := A).
      - eapply tr_subst_ren. 1: eassumption.
        apply WellRen_S.
      - rasimpl. eapply tr_var_known. 3: eassumption.
        + eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        + eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      - rasimpl. eapply tr_rename. 1,2: eassumption.
        apply WellRen_S.
    }
    eapply tr_ctx_cons with (A := (S >> S) ⋅ A) in hcar as hcara.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply WellRen_weak. apply WellRen_S.
    }
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{
      eapply tr_meta.
      { eapply tr_Pi. 1: eassumption.
        eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_substitution_sort. 1,2: eauto.
            eapply tr_subst_scons with (A := S ⋅ A).
            + eapply tr_subst_scons with (A := A).
              * eapply tr_subst_ren. 1: eassumption.
                apply WellRen_S.
              * {
                eapply tr_var_known. 3: eassumption.
                - eapply BasicMetaTheory.varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
                - eapply varty_meta.
                  { repeat econstructor. }
                  rasimpl. reflexivity.
              }
            + rasimpl. eapply tr_rename. 1,2: eauto.
              apply WellRen_S.
          - eapply tr_acc.
            + eapply tr_rename_sort. 1,2: eassumption.
              apply WellRen_weak. apply WellRen_S.
            + eapply tr_rename_sort. 1: eauto.
              * eapply tr_ctx_cons. 1: eassumption.
                rasimpl. eapply tr_rename_sort. 1,2: eassumption.
                do 2 apply WellRen_weak. apply WellRen_S.
              * apply WellRen_up. 2:{ rasimpl. reflexivity. }
                apply WellRen_up. 2: reflexivity.
                apply WellRen_weak. apply WellRen_S.
            + eapply tr_var_known. 3: eassumption.
              * eapply BasicMetaTheory.varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat econstructor. }
                rasimpl. reflexivity.
        }
        all: reflexivity.
      }
      all: reflexivity.
    }
    destruct ihp as [p' ihp].
    destruct ihA, ihR, iha, ihp.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros * ? ihA ? ihR ? iha ? ihp ? ihb ? ihr ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihp with (1 := hc).
    eapply change_type in ihp. 2:{ eapply tr_acc. all: eauto. }
    destruct ihp as [p' ihp].
    specialize ihb with (1 := hc).
    eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    specialize ihr with (1 := hc).
    eapply change_type in ihr.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply tr_subst_scons with (A := S ⋅ A).
      - eapply tr_subst_one. eassumption.
      - rasimpl. eassumption.
    }
    destruct ihr as [r' ihr].
    destruct ihA, ihR, iha, ihp, ihb, ihr.
    eexists _,_. split. 2: intuition (constructor ; eauto).
    econstructor. all: eauto.
  - intros ?? l * ? ihA ? ihR ? ihP. cbn zeta. intros ? ihp ? iha ? ihq ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    lazymatch type of ihp with
    | ∀ G', tr_ctx ?G G' → _ => eassert (hcap : tr_ctx G _)
    end.
    { eapply tr_ctx_cons. 1: eassumption.
      eapply tr_Pi.
      - eapply tr_rename_sort. 1,2: eassumption.
        apply WellRen_S.
      - eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_rename_sort. 1,2: eassumption.
            apply well_rcons_alt. 1: apply well_rcons_alt.
            + apply WellRen_weak. apply WellRen_S.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
          - eapply tr_rename_sort. 1: eassumption.
            + eapply tr_ctx_cons. 1: eassumption.
              eapply tr_rename_sort. 1,2: eassumption.
              apply well_rcons_alt. 1: apply well_rcons_alt.
              * apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
            + apply well_rcons_alt.
              * do 2 apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
        }
        all: destruct l ; reflexivity.
    }
    specialize ihp with (1 := hcap).
    eapply change_type in ihp.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply well_rcons_alt.
      - apply WellRen_weak. apply WellRen_S.
      - eapply varty_meta.
        { repeat constructor. }
        rasimpl. reflexivity.
    }
    destruct ihp as [p' ihp].
    specialize ihq with (1 := hc).
    eapply change_type in ihq. 2:{ eapply tr_acc. all: eauto. }
    destruct ihq as [q' ihq].
    destruct ihA, ihR, ihP, iha, ihp, ihq.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros ?? l * ? ihA ? ihR ? ihP. cbn zeta. intros ? ihp ? iha ? ihq ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    lazymatch type of ihp with
    | ∀ G', tr_ctx ?G G' → _ => eassert (hcap : tr_ctx G _)
    end.
    { eapply tr_ctx_cons. 1: eassumption.
      eapply tr_Pi.
      - eapply tr_rename_sort. 1,2: eassumption.
        apply WellRen_S.
      - eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_rename_sort. 1,2: eassumption.
            apply well_rcons_alt. 1: apply well_rcons_alt.
            + apply WellRen_weak. apply WellRen_S.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
          - eapply tr_rename_sort. 1: eassumption.
            + eapply tr_ctx_cons. 1: eassumption.
              eapply tr_rename_sort. 1,2: eassumption.
              apply well_rcons_alt. 1: apply well_rcons_alt.
              * apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
            + apply well_rcons_alt.
              * do 2 apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
        }
        all: destruct l ; reflexivity.
    }
    specialize ihp with (1 := hcap).
    eapply change_type in ihp.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply well_rcons_alt.
      - apply WellRen_weak. apply WellRen_S.
      - eapply varty_meta.
        { repeat constructor. }
        rasimpl. reflexivity.
    }
    destruct ihp as [p' ihp].
    specialize ihq with (1 := hc).
    eapply change_type in ihq. 2:{ eapply tr_acc. all: eauto. }
    destruct ihq as [q' ihq].
    destruct ihA, ihR, ihP, iha, ihp, ihq.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition eauto. econstructor; eauto using decoration, substs_decs_one.
      eapply substs_decs_two; eauto.
      econstructor; eauto.
      all:econstructor; eauto. 3:econstructor;eauto.
      8:econstructor; eauto.
      all:try econstructor.
      all:eauto using rename_dec.
      all:eapply substs_decs; eauto.
      all:unfold dec_subst; intro; destruct x; try destruct x; simpl; eauto using decoration, rename_dec.
  - intros * ? ihA ? iha ? ihb ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eexists _,_. eapply tr_obseq. all: eassumption.
  - intros * ? ihA ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    eexists _,_. eapply tr_obsrefl. all: eassumption.
  - intros * ? ihA ? iha ? ihP ? ihp ? ihb ? ihe ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    specialize ihb with (1 := hc). eapply change_type in ihb. 2: eassumption.
    destruct ihb as [b' ihb].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize ihp with (1 := hc).
    eapply change_type in ihp.
    2:{ eapply tr_substitution_one_sort. all: eassumption. }
    destruct ihp as [p' ihp].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{ eapply tr_obseq. all: eassumption. }
    destruct ihe as [e' ihe].
    destruct ihA, iha, ihP, ihp, ihb, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + eapply substs_decs_one. all: intuition assumption.
  - intros * ? ihA ? ihB ? ihe ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize ihB with (1 := hc). eapply keep_sort in ihB.
    destruct ihB as [B' ihB].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq. 2,3: eassumption.
      eapply tr_Sort. eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    destruct ihA, ihB, ihe, iha.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition eauto.
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    destruct ihA1, ihB1, ihA2, ihB2, ihe.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + intuition (constructor ; eauto).
  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? iha2. cbn zeta. intros ? hc.
    specialize ihA1 with (1 := hc). eapply keep_sort in ihA1.
    destruct ihA1 as [A1' ihA1].
    eapply tr_ctx_cons in hc as hca1. 2: eassumption.
    specialize ihB1 with (1 := hca1). eapply keep_sort in ihB1.
    destruct ihB1 as [B1' ihB1].
    specialize ihA2 with (1 := hc). eapply keep_sort in ihA2.
    destruct ihA2 as [A2' ihA2].
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2). eapply keep_sort in ihB2.
    destruct ihB2 as [B2' ihB2].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq.
      - eapply tr_Sort. eassumption.
      - eapply tr_Pi. all: eassumption.
      - eapply tr_Pi. all: eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha2 with (1 := hc). eapply change_type in iha2. 2: eassumption.
    destruct iha2 as [a2' iha2].
    destruct ihA1, ihB1, ihA2, ihB2, ihe, iha2.
    eexists _,_. split. 2: split. 2: intuition (constructor ; eauto).
    + econstructor. all: eauto.
    + constructor.
      * constructor.
      * eapply substs_decs_one. all: intuition (repeat constructor ; eauto).
      * eapply substs_decs_one. all: intuition eauto.
  - intros * ? iht ? ihAB ? hc.
    eapply iht in hc as tWt.
    eapply ihAB in hc as AconvB.
    eapply tr_conv; eauto.

  (* Conversion rules *)

  - intros * ??? hc. 
    eapply tr_var in v; eauto.
    destruct v as (A' & x' & h1 & h2 & h3).
    eapply tr_eq_conclude.
    7:eapply type_heq_refl. 8:eapply h1.
    all:eauto using validity_ty_ty.

  - intros.
    assert (⊢p Γ') as Γ'_Wf by (destruct H; eauto).
    eapply tr_eq_conclude.
    1-3:econstructor. 1:eapply dec_sort.
    3:eapply type_heq_refl.
    all:eauto using typing.

  (* case pi *)
  - intros. 
    rename A into A1. rename A' into A2.
    rename B into B1. rename B' into B2.
    assert (⊢p Γ') as Γ'_Wf by (destruct H2; eauto).
    eapply H0 in H2 as h0. eapply tr_eq_ty_sgeth in h0; eauto using typing, decoration.
    dependent destruction h0.
    rename t' into A1'. rename u' into A2'.

    
    assert (tr_ctx (Γ,, (i, A1)) (Γ',, (i, A1'))) as tr_ΓA by (eapply tr_ctx_cons'; eauto).

    eapply H1 in tr_ΓA as h1'.
    
    eapply tr_eq_ty_cons_geth_sort in h1'.
    6:eapply H7.
    all:eauto.
    destruct h1' as (B0 & B'0 & k). intuition eauto.
    destruct H13. rename B0 into B1'. rename B'0 into B2'.

    eapply type_heq_pi in H12; eauto.
    eapply tr_eq_conclude. 
    7:eapply H12.
    all:intuition eauto 8 using typing, decoration, cast_subst_refines.


  - intros.  destruct j. 2:econstructor.
    rename A into A1. rename A' into A2.
    rename B into B1. rename B' into B2.
    rename t into t1. rename t' into t2.
    assert (⊢p Γ') as Γ'_Wf by (destruct H3; eauto).
    eapply H0 in H3 as h0. eapply tr_eq_ty_sgeth in h0; eauto using typing, decoration.
    dependent destruction h0.
    rename t' into A1'. rename u' into A2'.

    
    assert (tr_ctx (Γ,, (i, A1)) (Γ',, (i, A1'))) as tr_ΓA by (eapply tr_ctx_cons'; eauto).

    eapply H1 in tr_ΓA as h1'.
    
    eapply tr_eq_ty_cons_geth_sort in h1'.
    6:eapply H8.
    all:eauto.
    destruct h1' as (B0 & B'0 & k). intuition eauto.
    destruct H14. rename B0 into B1'. rename B'0 into B2'.


    eapply H2 in tr_ΓA as h2'.
    eapply tr_eq_ty_cons_geth in h2'.
    8:eapply H13.
    all:eauto.
    destruct h2' as (t1' & t2' & k). intuition eauto.
    destruct H19.

    eapply type_heq_lam in H18; eauto.
    
    eapply tr_eq_conclude. 7:eapply H18.
    all:intuition eauto 8 using typing, decoration, cast_subst_refines.

  (* case app *)
  - intros.
    rename t1 into k1. rename t2 into k2.
    rename A into A1. rename B into B1. rename t into t1. rename u into u1. 
    rename A' into A2. rename B' into B2. rename t' into t2. rename u' into u2.
    destruct j. 2:econstructor.
    assert (⊢p Γ') as Γ'_Wf by (destruct H6; eauto).


    eapply H0 in H6 as h0. eapply tr_eq_ty_sgeth in h0; eauto using typing, decoration.
    dependent destruction h0. 
    rename t' into A1'. rename u' into A2'.


    assert (tr_ctx (Γ,, (i, A1)) (Γ',, (i, A1'))) as tr_ΓA 
      by (eapply tr_ctx_cons'; eauto).

    eapply H1 in tr_ΓA as h1'.
    
    eapply tr_eq_ty_cons_geth_sort in h1'.
    6:eapply H11.
    all:eauto.
    destruct h1' as (B0 & B'0 & k). intuition eauto.
    destruct H17. rename B0 into B1'. rename B'0 into B2'.
    
    eapply H2 in H6 as h2. eapply tr_eq_ty_geth in h2.
    6:{ eapply meta_conv. 1:eapply type_heq_pi.
        6:eapply H16. all:eauto. }
    all:eauto using typing, decoration, meta_conv, meta_lvl.
    dependent destruction h2. rename t' into t1'. rename u' into t2'.
    

    assert (Γ' ⊨⟨ i ⟩ u1 : A1 ↦ A1' = u2 : A2 ↦ A2').
    { destruct i.
      * eapply H5 in H6 as h5. eapply tr_eq_ty_geth in h5.
        6:eapply H11. all:eauto.
      * eapply H3 in H6 as h3. eapply H4 in H6 as h4.
        eapply tr_eq_prop_geth in  h4. 6:eapply H11. 6:eapply h3.
        all:eauto. }

    dependent destruction H22. 

    eapply type_heq_app in H26. 6:eapply meta_conv. 6:eapply H21. 
    all:eauto using typing, meta_lvl.

    eapply tr_eq_conclude. 7:eapply H26. 
    all:eauto 8 using typing, decoration, cast_subst_refines, substs_decs_one.

  (* case Nat *)
  - intros.
    assert (⊢p Γ') as Γ'_Wf by (destruct H; eauto).
    eapply tr_eq_conclude.
    1-3:econstructor. 1:eapply dec_sort.
    3:eapply type_heq_refl.
    all:eauto using typing, meta_conv, meta_lvl.

  (* case zero *)
  - intros.
    assert (⊢p Γ') as Γ'_Wf by (destruct H; eauto).
    eapply tr_eq_conclude.
    1-3:econstructor. 1:eapply dec_nat.
    3:eapply type_heq_refl.
    all:eauto using typing, meta_conv, meta_lvl.

  (* case succ *)
  - intros. rename t' into u.
    assert (⊢p Γ') as Γ'_Wf by (destruct H0; eauto).

    eapply H in H0 as h'.
    eapply tr_eq_ty_geth in h'.
    4,5:eapply type_nat. all:eauto using decoration.
    2:eapply type_heq_refl; eauto using typing.

    dependent destruction h'.

    eapply type_heq_succ in H5; eauto.

    eapply tr_eq_conclude.
    7:eapply H5.
    all:eauto using typing, decoration.

  (* case rec *)
  - intros.  destruct l. 2:econstructor.
    rename P into P1. rename P' into P2. rename p_succ into p_succ1. rename p_succ' into p_succ2.
    rename p_zero into p_zero1. rename p_zero' into p_zero2. rename t into t1. rename t' into t2.
    assert (⊢p Γ') by (destruct H4; eauto).

    eapply tr_ctx_cons with (i := ty 0) in H4 as hcn.
    2:{ eapply tr_Nat. eassumption. }

    assert (exists e, Γ' ⊢p< prop > e : heq (Ax (ty 0)) (Sort (ty 0)) (Sort (ty 0)) Nat Nat).
    1:{ eexists. eapply type_heq_refl; eauto using typing. }
    destruct H6.
        

    eapply H0 in hcn as h0.

    eapply tr_eq_ty_cons_geth in h0. 9:eapply H6.
    8:{ eapply meta_conv. 1:eapply type_heq_refl.
        1,2:eapply type_sort.
        Unshelve. 7,8:exact (Sort (ty n)).
        4-7:shelve.
        3:rasimpl; reflexivity.
        all:eapply ctx_extend_Wt; eauto using typing.
    } 
    all:eauto using typing, decoration, ctx_typing.

    destruct h0 as (P1' & P2' & ?). intuition eauto. destruct H12.

    assert (exists e, Γ' ⊢p< prop > e : heq (Ax (ty n)) (Sort (ty n)) (Sort (ty n)) (P1'<[zero..]) (P2'<[zero..])).
    { eexists. eapply subst_ty. 3:eapply H11. 1:eauto.
      Unshelve. 3:exact ((heq_refl (ty 0) Nat zero) .:(zero .: (zero .: var))).
      1:econstructor. 1:econstructor. 1:econstructor.
      1:ssimpl; eapply subst_id; eauto.
      1-3:ssimpl; eauto using typing.
      1:rewrite heq_subst; rasimpl.
      1:eapply type_heq_refl; eauto using typing.
      rewrite heq_subst; f_equal; rasimpl; reflexivity. }
    destruct H12.

    eapply tr_eq_ty_geth in H1. 6:eapply H12.
    all:eauto using typing, substs_decs_one, decoration.
    2,3:eapply subst_ty; eauto using subst_one, typing.

    inversion H1. rename t' into p_zero1'. rename u' into p_zero2'.

    assert (tr_ctx ((Γ,, (ty 0, Nat)),, (ty n, P1)) (Γ',, (ty 0, Nat) ,, (ty n, P1')))
      by (eapply tr_ctx_cons'; eauto).

    eapply H2 in H18.

    eapply ctx_extend2_Wt in H10 as h. 2:eapply H9.

    eapply tr_eq_ty_cons2_geth in H18.
    11:eapply H11.
    11:{  
      Unshelve. 9:exact (P1'<[succ (var 1) .: S >> (S >> var)]). 9:exact (P2'<[succ (var 1) .: S >> (S >> var)]).
      2-8:shelve.
      eapply subst_ty.
      3:eapply H11. Unshelve. 
      10:eapply (_ .: ((succ (var 4)) .: ((succ (var 5)) .: (S >> S >> S >> S >> S >> S >> var)))). 4-9:shelve.

      2:econstructor. 2:econstructor. 2:econstructor.
      2-5:asimpl_unsafe.
      3,4:econstructor.
      3,4:econstructor.
      4,6:eapply varty_meta. 
      6:econstructor;econstructor; econstructor; econstructor; econstructor.
      4:econstructor;econstructor; econstructor; econstructor; econstructor; econstructor.
      4,5:eauto.
      5:rewrite heq_subst; rasimpl; eapply type_heq_succ.
      7:{ Unshelve. 8:exact (var 3). 2-7:shelve.
          econstructor. 
          2:eapply varty_meta.
          2:econstructor;econstructor;econstructor;econstructor.
          2:rasimpl; rewrite heq_ren; f_equal; rasimpl; reflexivity. 
          rasimpl in h. rasimpl. eapply h. }
        5,6:econstructor.
        6,8:eapply varty_meta.
      8:econstructor;econstructor; econstructor; econstructor; econstructor.
      6:econstructor;econstructor; econstructor; econstructor; econstructor; econstructor.
      6,7:eauto.
      7:rewrite heq_subst; rasimpl; f_equal; rasimpl; reflexivity.
      all:try (rasimpl in h; rasimpl; eapply h).
      dependent destruction h.
      dependent destruction h.
      dependent destruction h.
      dependent destruction h.
      dependent destruction h.
      eapply WellSubst_morphism.
      Unshelve. 13:exact ((((((var >> ren_term S) >> ren_term S) >> ren_term S) >> ren_term S) >> ren_term S) >> ren_term S).
      5-12:shelve.
      4:eapply WellSubst_weak.
      4:eapply WellSubst_weak.
      4:eapply WellSubst_weak.
      4:eapply WellSubst_weak.
      4:eapply WellSubst_weak.
      4:eapply WellSubst_weak. 1:reflexivity.
      3:eapply subst_id; eauto.
      2:rasimpl; reflexivity.
      all:eauto using typing.
      1:rasimpl in H20; rasimpl; eapply H20.
      rasimpl in H19; rasimpl; eauto. }
      all:eauto using typing, decoration.
      2,3:eapply subst_dec; eauto.
      (* 2,3:intro x'; destruct x'; eauto using dterm. *)
      2,3:eapply subst_ty. 4:eapply H9. 7:eapply H10.
      all:eauto using ctx_typing, validity_ty_ctx.
      2,3:econstructor.
      2-5:ssimpl.
      3,5:eapply type_succ.
      3,4:econstructor. 4,6:eapply varty_meta.
      4,6:econstructor;econstructor.
      all:eauto using ctx_typing, validity_ty_ctx.
      2,3:ssimpl.
      2,3:eapply WellSubst_morphism.
      Unshelve. 15,12:exact ((var >> ren_term (S >> S))). 10-13:shelve.
      5,9:eapply WellSubst_weak_two. 2,9,3,10:reflexivity. 
      all:eauto using subst_id, ctx_typing, validity_ty_ctx.
      2,3:unfold pointwise_relation; intro x'; destruct x; reflexivity.

      destruct H18 as (p_succ1' & p_succ2' & ?). intuition eauto. destruct H23.

      eapply H3 in H4 as h3.
      eapply tr_eq_ty_sgeth in h3; eauto using decoration, typing.
      inversion h3. rename t' into t1'. rename u' into t2'.

      eapply type_heq_rec in H27.
      11:eapply H17.
      10:eapply H11.
      10: eapply meta_conv. 10:eapply H22.
      10:{ f_equal; rasimpl. all:eapply subst_term_morphism;eauto.
          all:unfold pointwise_relation;intros.
          1,2:destruct a; unfold ">>"; simpl; reflexivity. }
      all:eauto.
      
      eapply tr_eq_conclude. 7:eapply H27.
      all:eauto using typing, decoration, substs_decs_one.

  - intros. rename A into A1. rename A' into A2. rename a into a1. rename a' into a2.
    rename R into R1. rename R' into R2.
    assert (⊢p Γ') as Γ'_Wf by (destruct H3; eauto).

    specialize H0 with (1:=H3).
    eapply tr_eq_ty_sgeth in H0; eauto using decoration, typing.
    destruct H0. rename t' into A1'. rename u' into A2'.



    assert (tr_ctx ((Γ,, (ty n, A1)),, (ty n, S ⋅ A1)) ((Γ',, (ty n, A1')),, (ty n, S ⋅ A1'))).
    { eapply tr_ctx_cons'. 1:eapply tr_ctx_cons'.
      all:eauto using rename_dec. eapply type_ren; eauto using WellRen_S, validity_ty_ctx, ctx_typing. }

    specialize H1 with (1:=H8).
    eapply tr_eq_ty_cons2_geth in H1.
    10:eapply H7.
    10:{eapply type_ren. 1:eapply H7.
      2:eauto using WellRen_S, WellRen_weak.
      2:rewrite (heq_ren ((S >> S) >> S) ); f_equal.
      Unshelve. 11:exact (S ⋅ A2'). 
      4-11:shelve. 2,3:rasimpl;reflexivity.
      eapply ctx_extend_Wt; eauto using validity_ty_ctx. }
    10:{
      eapply meta_conv.
      1:eapply type_heq_refl.
      2:eapply type_sort. 1:econstructor.
      Unshelve. 11:exact prop. 10:exact (Sort prop). 9:exact (Sort prop). 4-8:shelve.
      3:simpl; f_equal. 1,2:eapply ctx_extend2_Wt; eauto using type_ren, WellRen_S, ctx_typing. }
    all:eauto using decoration, rename_dec.
    2,3:eauto 7 using typing, ctx_typing, type_ren, WellRen_S.
    destruct H1 as (R1' & R2' & ?). intuition eauto.
    destruct H13.

    specialize H2 with (1:=H3).
    eapply tr_eq_ty_geth in H2. 6:eapply H7. all:eauto.
    destruct H2. rename t' into a1'. rename u' into a2'.


    rasimpl in H12.
    eapply type_heq_acc in H16.  
    6:eapply meta_conv. 6:rasimpl. 6:eapply H12. 2:eapply H10. 3:eapply H11.
    4:f_equal; rasimpl; reflexivity.
    all:eauto.
    
    eapply tr_eq_conclude.
    7:eapply H16.
    all:eauto using decoration, typing.
    

  - intros * _ _ _ ihA _ _ _ ihR _ _ _ ihP * _ ihp _ iha _ ihq1 _ ihq2 _ _ * hc.
    destruct l. 2:econstructor.
    assert (⊢p Γ') as Γ'_Wf by (destruct hc;eauto).
    rename A into A1. rename A' into A2. rename R into R1. rename R' into R2.
    rename P into P1. rename P' into P2. rename p into p1. rename p' into p2.
    rename a into a1. rename a' into a2. rename q into q1. rename q' into q2.
    specialize ihA with (1:=hc).
    specialize iha with (1:=hc).
    specialize ihq1 with (1:=hc).
    specialize ihq2 with (1:=hc).
    
    eapply tr_eq_ty_sgeth in ihA; eauto using typing, decoration.
    destruct ihA. rename t' into A1'. rename u' into A2'.

    eapply tr_eq_ty_geth in iha. 6:eapply H3. all:eauto.
    destruct iha. rename t' into a1'. rename u' into a2'.


    assert (tr_ctx ((Γ,, (ty n, A1)),, (ty n, S ⋅ A1)) ((Γ',, (ty n, A1')),, (ty n, S ⋅ A1'))).
    { eapply tr_ctx_cons'. 1:eapply tr_ctx_cons'.
      all:eauto using rename_dec. eapply type_ren; eauto using WellRen_S, validity_ty_ctx, ctx_typing. }

    specialize ihR with (1:=H9).
    eapply tr_eq_ty_cons2_geth in ihR.
    10:eapply H3.
    10:{eapply type_ren. 1:eapply H3.
      2:eauto using WellRen_S, WellRen_weak.
      2:rewrite (heq_ren ((S >> S) >> S) ); f_equal.
      Unshelve. 11:exact (S ⋅ A2'). 
      4-11:shelve. 2,3:rasimpl;reflexivity.
      eapply ctx_extend_Wt; eauto using validity_ty_ctx. }
    10:{
      eapply meta_conv.
      1:eapply type_heq_refl.
      2:eapply type_sort. 1:econstructor.
      Unshelve. 11:exact prop. 10:exact (Sort prop). 9:exact (Sort prop). 4-8:shelve.
      3:simpl; f_equal. 1,2:eapply ctx_extend2_Wt; eauto using type_ren, WellRen_S, ctx_typing. }
    all:eauto using decoration, rename_dec.
    2,3:eauto 7 using typing, ctx_typing, type_ren, WellRen_S.
    destruct ihR as (R1' & R2' & ?). intuition eauto.
    destruct H15.


    eapply tr_tm_get in ihq1. 2:econstructor; eauto. 2:eauto using typing.
    eapply tr_tm_get in ihq2. 2:econstructor; eauto. 2:eauto using typing.
    destruct ihq1 as (q1' & ? & ?).
    destruct ihq2 as (q2' & ? & ?).


    assert (tr_ctx ((Γ,, (ty n, A1))) ((Γ',, (ty n, A1')))).
    { eapply tr_ctx_cons'; eauto. }
    specialize ihP with (1:= H19).

    eapply tr_eq_ty_cons_geth_sort in ihP. 6:eassumption. all: eauto using decoration, typing, ctx_typing.
    destruct ihP as (P1' & P2' & ?). intuition eauto. destruct H25.


    pose (R_1' := (1 .: (0 .: (S >> S))) ⋅ R1').
    pose (P_1' := (1 .: (S >> S >> S)) ⋅ P1').
    pose (B1' := Pi (ty n) (ty n0 ) (S ⋅ A1') (Pi prop (ty n0) R_1' P_1')).
    pose (P01' := (1.: (S >> S)) ⋅ P1').

    pose (R_2' := (1 .: (0 .: (S >> S))) ⋅ R2').
    pose (P_2' := (1 .: (S >> S >> S)) ⋅ P2').
    pose (B2' := Pi (ty n) (ty n0 ) (S ⋅ A2') (Pi prop (ty n0) R_2' P_2')).
    pose (P02' := (1.: (S >> S)) ⋅ P2').

    rename B into B1.
    assert (B1 ⊏ B1') as B1_dec_B1'.
    { unfold B1, B1'. econstructor. 2:econstructor. 2,3:unfold R_, P_, R_1', R_2'. all:eauto using rename_dec. }

    assert (Pi (ty n) (ty n0) (S ⋅ A2) (Pi prop (ty n0) ((1 .: (0 .: S >> S)) ⋅ R2) ((1 .: (S >> S) >> S) ⋅ P2)) ⊏ B2')
      as B2_dec_B2'.
    { unfold B2', R_2', P_2'. econstructor. 2:econstructor. all:eauto using rename_dec. }

    rename P'' into P01.
    assert (P01 ⊏ P01') as P01_dec_P01'.
    { unfold P01, P01'. eauto using rename_dec. }
    assert ((1 .: S >> S) ⋅ P2 ⊏ P02') as P02_dec_P02'.
    { unfold P02'. eauto using rename_dec. }

    eassert (_ ⊢p< _ > B2' : _) as B2'Wt by eauto using BWt.
    eassert (_ ⊢p< _ > B1' : _) as B1'Wt by eauto using BWt.

    eapply type_inv in B1'Wt as temp. dependent destruction temp.
    eapply type_inv in B2'Wt as temp. dependent destruction temp.

    eassert (_ ⊢p< _ > R_1' : _) as R_1'Wt by eauto using R0Wt.
    eassert (_ ⊢p< _ > R_2' : _) as R_2'Wt by eauto using R0Wt.
    eassert ((_ ,, (_, R_1')) ⊢p< _ > P_1' : _) as P_1'Wt by eauto using P0Wt.
    eassert ((_ ,, (_, R_2')) ⊢p< _ > P_2' : _) as P_2'Wt by eauto using P0Wt.
    assert (⊢p (((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (ty n, (S >> S) ⋅ S ⋅ A1')),, (ty n, S ⋅ (up_ren S >> S) ⋅ S ⋅ A2')),, 
      (prop, heq (ty n) ((S >> S) ⋅ (S >> S) ⋅ S ⋅ A1') ((S >> S) ⋅ (up_ren S >> S) ⋅ S ⋅ A2') (var 1) (var 0))) as ΓASA.
    { assert (∀ x y, x = y -> ⊢p x -> ⊢p y) by (intros; subst; eauto).
        eapply H25. 2:eapply ctx_extend2_Wt.
        2,3:eapply type_ren. 4,8:eapply WellRen_S.
        2:eapply H1. 4:eapply H2.
        2:econstructor. 3:eapply H1.
        4:econstructor. 5:eapply H2.
        all:eauto.
        rasimpl. reflexivity. }

    assert (⊢p ((((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (ty n, (S >> S) ⋅ S ⋅ A1')),, (ty n, S ⋅ (up_ren S >> S) ⋅ S ⋅ A2')),, 
      (prop, heq (ty n) ((S >> S) ⋅ (S >> S) ⋅ S ⋅ A1') ((S >> S) ⋅ (up_ren S >> S) ⋅ S ⋅ A2') (var 1) (var 0))),,
      (prop, (S >> S) ⋅ upRen_term_term (S >> S) ⋅ R_1') ) as ΓAAR1.
    { eassert _ as h.
      2:econstructor.
      3:exact h.
      2:eauto using validity_ty_ctx.
      unfold R_1'. rasimpl. eapply type_ren; eauto.
      1:rasimpl; rasimpl in ΓASA; eapply ΓASA.
      econstructor. 1:econstructor. 1:ssimpl; eauto 7 using WellRen_S, WellRen_weak.
      1,2:ssimpl;eapply varty_meta.
      1,3:eauto 8 using varty.
      all:rasimpl;reflexivity. }
      
    assert (⊢p ((((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (ty n, (S >> S) ⋅ S ⋅ A1')),, (ty n, S ⋅ (up_ren S >> S) ⋅ S ⋅ A2')),, 
      (prop, heq (ty n) ((S >> S) ⋅ (S >> S) ⋅ S ⋅ A1') ((S >> S) ⋅ (up_ren S >> S) ⋅ S ⋅ A2') (var 1) (var 0))),,
      (prop, (up_ren S >> S) ⋅ upRen_term_term (up_ren S >> S) ⋅ R_2')) as ΓAAR2.
    { eassert _ as h.
      2:econstructor.
      3:exact h.
      2:eauto using validity_ty_ctx.
      unfold R_2'. rasimpl. eapply type_ren; eauto.
      1:rasimpl; rasimpl in ΓASA; eapply ΓASA.
      econstructor. 1:econstructor. 1:ssimpl; eauto 7 using WellRen_S, WellRen_weak.
      1,2:ssimpl;eapply varty_meta.
      1,3:eauto 8 using varty.
      all:rasimpl;reflexivity. }


    assert (⊢p (((((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (ty n, (S >> S) ⋅ S ⋅ A1')),, (ty n, S ⋅ (up_ren S >> S) ⋅ S ⋅ A2')),, 
      (prop, heq (ty n) ((S >> S) ⋅ (S >> S) ⋅ S ⋅ A1') ((S >> S) ⋅ (up_ren S >> S) ⋅ S ⋅ A2') (var 1) (var 0))),,
      (prop, (S >> S) ⋅ upRen_term_term (S >> S) ⋅ R_1')),, (prop, S ⋅ (up_ren S >> S) ⋅ upRen_term_term (up_ren S >> S) ⋅ R_2')) as ΓAAR1R2.
    { 
      eassert _ as h.
      2:econstructor.
      3:exact h.
      2:eauto using validity_ty_ctx.
      rasimpl. eapply type_ren; eauto.
      1:rasimpl in ΓAAR1; rasimpl; eassumption.
      econstructor. 1:econstructor. all:ssimpl.
      1:eauto 8 using WellRen_S, WellRen_weak.
      1,2:eapply varty_meta.
      1,3:eauto 6 using varty.
      all:rasimpl; reflexivity. }

    assert (⊢p (((((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (ty n, (S >> S) ⋅ S ⋅ A1')),, (ty n, S ⋅ (up_ren S >> S) ⋅ S ⋅ A2')),, 
      (prop, heq (ty n) ((S >> S) ⋅ (S >> S) ⋅ S ⋅ A1') ((S >> S) ⋅ (up_ren S >> S) ⋅ S ⋅ A2') (var 1) (var 0))),,
      (prop, (S >> S) ⋅ upRen_term_term (S >> S) ⋅ R_1')),, (prop, S ⋅ (up_ren S >> S) ⋅ upRen_term_term (up_ren S >> S) ⋅ R_2') ,,
      (prop, heq prop ((S >> S) ⋅ (S >> S) ⋅ upRen_term_term (S >> S) ⋅ R_1') 
          ((S >> S) ⋅ (up_ren S >> S) ⋅ upRen_term_term (up_ren S >> S) ⋅ R_2') (var 1) (var 0))) as ΓAAR.
    {  
      eassert _ as h.
      2:econstructor.
      3:exact h.
      2:eauto using validity_ty_ctx.
      eapply type_heq.
      1,2:rasimpl;eapply type_ren; eauto.
      1,3:rasimpl; rasimpl in ΓAAR1R2; eassumption.
      1,2:econstructor. 3:econstructor.
      1-5:ssimpl.
      1,3:eauto 8 using WellRen_weak, WellRen_S.
      1-3:eapply varty_meta.
      1,3,5:eauto 7 using varty.
      1-3:rasimpl;reflexivity.
      1,2:econstructor.
      1,3:rasimpl; rasimpl in ΓAAR1R2; eassumption.
      1,2:eapply varty_meta.
      1,3:eauto using varty.
      all:rasimpl; reflexivity. }


    assert (exists e', Γ',, (ty n, A1'),, (ty n, S ⋅ A2'),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0)) 
      ⊢p< prop > e' : heq (Ax (Ru (ty n) (ty n0))) (Sort (Ru (ty n) (ty n0))) (Sort (Ru (ty n) (ty n0))) ((S >> S) ⋅ B1') (((up_ren S >> S) ⋅ B2')))
      as (? & B1'_eq_B2').
    { eexists. 
      eapply type_heq_pi; fold ren_term.
      6:change (heq (Ax (ty n0)) (Sort (ty n0)) (Sort (ty n0))) with (heq (Ax (Ru prop (ty n0))) (Sort (Ru prop (ty n0))) (Sort (Ru prop (ty n0)))).
      6:eapply type_heq_pi; fold ren_term.
      10:{ 
        eapply type_ren.
        1:eapply H14.
        Unshelve.
        6:exact (3 .: (4  .: (5 .: (0 .: (1 .: (2 .: (S >> S >> S >> S >> S >> S))))))).
        4,5:shelve.
        3:rasimpl; rewrite heq_ren;unfold R_1', R_2'; rasimpl;reflexivity.
        1:eassumption.

        econstructor. 1:econstructor. 1:econstructor. 1:econstructor. 1:econstructor. 1:econstructor.
        all:ssimpl. 1:eauto 7 using WellRen_weak, WellRen_S.
        all:eapply varty_meta.
        1,3,5,7,9,11:eauto 7 using varty.
        all:rasimpl;eauto.
        all:rewrite heq_ren; rewrite heq_ren; rasimpl;f_equal. }
      10:{
        eapply type_ren. 1:eapply H24.
        2:{eapply WellRen_weak, WellRen_weak, WellRen_weak.
          1:eapply WellRen_up. 1:eapply WellRen_up. 1:eapply WellRen_up. 
          1:eapply WellRen_weak, WellRen_weak, WellRen_weak. 1:eapply WellRen_id.
          all:rasimpl;eauto.
          rewrite heq_ren. f_equal; rasimpl; reflexivity. }
        2:rewrite heq_ren; unfold P_1', P_2'; rasimpl; f_equal.
      econstructor. 1:econstructor. 1:econstructor.
      1:eassumption.
      3:inversion ΓAAR; eassumption.
      1:{ dependent destruction ΓAAR. dependent destruction ΓAAR. dependent destruction ΓAAR. eauto. }
      1:{ dependent destruction ΓAAR. dependent destruction ΓAAR.  eauto. } }
      6:{ dependent destruction ΓAAR. dependent destruction ΓAAR.  dependent destruction ΓAAR.  eauto. }
      5:{ eapply type_ren.
        1:eapply H3. 2:eauto using WellRen_weak, WellRen_S.
        1:eauto using validity_ty_ctx.
        rewrite heq_ren; rasimpl; reflexivity. }
      1,2:rasimpl;eapply type_ren; eauto using validity_ty_ctx, WellRen_S, WellRen_weak.

      4:{ unfold P_1',P_2';rasimpl;eapply type_ren. 1:eassumption.
          1:rasimpl in ΓAAR1; eassumption.
          2:eauto.
          econstructor; ssimpl.
          1:eauto 8 using WellRen_S, WellRen_weak. 
          eapply varty_meta.
          1:eauto using varty.
          rasimpl. reflexivity. }
      4:{ unfold P_1',P_2';rasimpl;eapply type_ren. 1:eassumption.
          1:rasimpl in ΓAAR2; eassumption.
          2:eauto.
          econstructor; ssimpl.
          1:eauto 8 using WellRen_S, WellRen_weak. 
          eapply varty_meta.
          1:eauto using varty.
          rasimpl. reflexivity. }
      3:dependent destruction ΓAAR2; eassumption.
      1:{ eapply meta_tm_conv.
          1:eapply type_ren. 
          1:eapply meta_lvl. 
          1:eapply type_pi.
          1:eapply R_1'Wt. 1:eapply P_1'Wt.
          1,4:eauto.
          2:eauto using WellRen_S, WellRen_weak, WellRen_up.
          2:rasimpl;reflexivity.
          eassert _.
          2:econstructor.
          3:eassumption.
          2:eauto using validity_ty_ctx.
          rasimpl. eapply type_ren; eauto using validity_ty_ctx, WellRen_S, WellRen_weak. }
      1:{ eapply meta_tm_conv.
          1:eapply type_ren. 
          1:eapply meta_lvl. 
          1:eapply type_pi.
          1:eapply R_2'Wt. 1:eapply P_2'Wt.
          1,4:eauto.
          2:eauto using WellRen_S, WellRen_weak, WellRen_up.
          2:rasimpl;reflexivity.
          eassert _.
          2:econstructor.
          3:eassumption.
          2:eauto using validity_ty_ctx.
          rasimpl. eapply type_ren; eauto using validity_ty_ctx, WellRen_S, WellRen_weak. } 
    }


    assert (exists e, (((((Γ',, (ty n, A1')),, (ty n, S ⋅ A2')),, (prop, heq (ty n) ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0))),, 
      (Ru (ty n) (ty n0), (S >> S) ⋅ B1')),, (Ru (ty n) (ty n0), ((up_ren S >> S) >> S) ⋅ B2')),, 
      (prop, heq (Ru (ty n) (ty n0)) ((((S >> S) >> S) >> S) ⋅ B1') ((((up_ren S >> S) >> S) >> S) ⋅ B2') (var 1) (var 0)) 
      ⊢p< prop > e : heq (Ax (ty n0)) (Sort (ty n0)) (Sort (ty n0)) (((up_ren (S >> S) >> S) >> S) ⋅ P01') ((up_ren ((up_ren S >> S) >> S) >> S) ⋅ P02'))
      as (? & P01'_eq_P02').
    { eexists.
      eapply type_ren.
      1:eapply H24. 
      1:eapply ctx_extend2_Wt; eauto.
      1:eapply WellRen_weak, WellRen_weak, WellRen_S.
      rasimpl. rewrite heq_ren. f_equal; unfold P01', P02'; rasimpl; eauto.
      eapply ren_term_morphism;eauto.
      unfold pointwise_relation; intros.
      destruct a. 2:destruct a. 3:destruct a. 4:destruct a.
      all:reflexivity. }



    assert ((Γ',, (ty n, A1')),, (ty n, S ⋅ A1') ⊢r (1 .: (0 .: S >> S)) : (Γ',, (ty n, A1')),, (ty n, S ⋅ A1')).
    { econstructor. 1:econstructor. 1:ssimpl; eauto using WellRen_weak, WellRen_S.
      all:eapply varty_meta.
      1,3:econstructor. 1:econstructor. all:rasimpl;reflexivity. }


    assert (tr_ctx ((Γ,, (ty n, A1)),, (Ru (ty n) (ty n0), B1)) ((Γ',, (ty n, A1')),, (Ru (ty n) (ty n0), B1'))) as trΓAB
    by eauto using  tr_ctx_cons'.

    specialize ihp with (1:=trΓAB).

    eapply tr_eq_ty_cons2_geth in ihp.
    10:eapply H3.
    10:eapply B1'_eq_B2'.
    10:eapply P01'_eq_P02'.
    8,9:eapply P00Wt; eauto.
    all:eauto.

    destruct ihp as (p1' & p2' & k1 & k2 & k3 & k4 & k5 & k6). 


    eapply type_heq_accel in k6; eauto. 2:rasimpl in H14; rasimpl; eapply H14.

    eapply tr_eq_conclude. 7:eapply k6.
    all:eauto using typing, decoration, substs_decs_one.


  (* case obseq *)
  - intros. 
    rename A into A1. rename A' into A2. rename a into a1. rename a' into a2.
    rename b into b1. rename b' into b2.
    assert (⊢p Γ') as Γ'_Wf by (destruct H2; eauto).

    eapply H in H2 as h. clear H.
    eapply H0 in H2 as h0. clear H0.
    eapply H1 in H2 as h1. clear H1.

    eapply tr_eq_ty_sgeth in h; eauto using decoration, typing.
    destruct h.

    eapply tr_eq_ty_geth in h0; eauto. 
    eapply tr_eq_ty_geth in h1; eauto. 
    dependent destruction h0. dependent destruction h1.
    
    eapply type_heq_obseq in H14. 
    6:eapply H9. all:eauto.
    
    eapply tr_eq_conclude. 7:eapply H14.
    all:eauto using decoration, typing.

  (* case cast *)
  - intros. destruct i. 2:econstructor.
    rename A into A1. rename A' into A2. rename a into a1. rename a' into a2.
    rename B into B1. rename B' into B2. rename e into e1. rename e' into e2.
    assert (⊢p Γ') as Γ'_Wf by (destruct H5; eauto).

    eapply H in H5 as h'. clear H.
    eapply H0 in H5 as h0'. clear H0.
    eapply H4 in H5 as h4'. clear H4.
    eapply H1 in H5 as h1'. clear H1.
    eapply H2 in H5 as h2'. clear H2.

    eapply tr_eq_ty_sgeth in h'; eauto using typing, decoration.
    eapply tr_eq_ty_sgeth in h0'; eauto using typing, decoration.
    destruct h'. destruct h0'.
    rename t' into A1'. rename u' into A2'. rename t'0 into B1'. rename u'0 into B2'.

    eapply tr_eq_ty_geth in h4'. 6:eapply H4. all:eauto. destruct h4'.
    rename t' into a1'. rename u' into a2'.

    eapply tr_tm_get in h1'. 2:econstructor;eauto using decoration.
    2:eauto using typing.
    eapply tr_tm_get in h2'. 2:econstructor;eauto using decoration.
    2:eauto using typing.
    destruct h1'. destruct h2'. intuition eauto.

    eapply type_heq_cast in H13 as h13. 4:eapply H19. all:eauto.
    eapply type_heq_cast in H14 as h14. 4:eapply H20. all:eauto.
    eapply type_heq_trans' in h14. 5:eauto. all:eauto using typing.
    destruct h14.

    eapply type_heq_sym in h13; eauto using typing.
    eapply type_heq_trans' in H17. 5:eauto. all:eauto using typing.
    destruct H17.

    eapply tr_eq_conclude.
    7:eapply H17.
    all:eauto using typing, decoration.

  - intros *  ? ihe ? ihA ? iha ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    specialize ihe with (1 := hc). eapply change_type in ihe.
    2:{
      eapply tr_obseq. 2,3: eassumption.
      eapply tr_Sort. eassumption.
    }
    destruct ihe as [e' ihe].
    specialize iha with (1 := hc). eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    destruct ihA, ihe, iha.
    intuition eauto.
    eapply tr_eq_conclude_by_refl.
    4:eapply conv_cast_refl; eauto.
    all:eauto using decoration.


  - intros * ? ihA1 ? ihB1 ? ihA2 ? ihB2 ? ihe ? ihf ? *  hc.
    specialize ihA1 with (1 := hc).
    eapply keep_sort in ihA1. destruct ihA1 as (A' & ihA1).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB1 with (1 := hca).
    eapply keep_sort in ihB1. destruct ihB1 as (B' & ihB1).
    specialize ihA2 with (1 := hc).
    eapply keep_sort in ihA2. destruct ihA2 as (A'2 & ihA2).
    eapply tr_ctx_cons in hc as hca2. 2: eassumption.
    specialize ihB2 with (1 := hca2).
    eapply keep_sort in ihB2. destruct ihB2 as (B'2 & ihB2).
    specialize ihf with (1 := hc).
    eapply change_type in ihf. 2:{ eapply tr_Pi. all: eassumption. }
    destruct
      ihA1 as (? & ? & _),
      ihB1 as (? & ? & _),
      ihA2 as (? & ? & _),
      ihB2 as (? & ? & _),
      ihf as (? & ? & ?). intuition eauto.
      
  
    specialize ihe with (1 := hc).
    eapply tr_tm_get in ihe.
    2:econstructor. 2-4:econstructor. all:eauto.
    2:econstructor; eauto using typing, validity_ty_ctx.
    destruct ihe. destruct H8.

    eapply tr_eq_conclude_by_refl.
    4:eapply conv_cast_pi. 8:eapply H11. 8:eapply H7.
    all:eauto using decoration.
    unfold t8, t7, t6, t5, B2', B1', A2', A1'.
    econstructor; eauto.
    econstructor; eauto.
    2:econstructor; eauto using rename_dec, decoration.
    2:econstructor; eauto using rename_dec, decoration.
    2:econstructor; eauto using rename_dec, decoration.
    2:econstructor; eauto using rename_dec, decoration.
    eapply substs_decs; eauto.
    unfold dec_subst. intros.
    destruct x1;simpl.
    2:unfold ">>";econstructor.
    econstructor; eauto 8 using decoration, rename_dec.

  - intros. destruct l. 2:econstructor. rename t' into u.
    eapply H in H1 as h1.
    eapply H0 in H1 as h0. clear H H0. 
    dependent destruction h1. 
    
    eapply tr_eq_ty_sgeth in h0; eauto using decoration, typing, validity_ty_ctx.
    dependent destruction h0. rename t'0 into A''. rename u'0 into B'.

    assert (A' ~ A'') by eauto using dec_to_sim, sim_sym, sim_trans.
    eapply sim_heq_same_ctx in H11; eauto using validity_ty_ty.
    destruct H11. eapply type_heq_trans' in H10. 5:eapply H11. 
    all:eauto using validity_ty_ty.
    destruct H10.

    eapply type_heq_cast in H3 as H3'; eauto using validity_ty_ty, type_hetero_to_homo.
    eapply type_heq_cast in H4 as H4'; eauto using validity_ty_ty, type_hetero_to_homo.

    eapply type_heq_trans' in  H4'. 5:eapply H5. all:eauto using typing, type_hetero_to_homo, validity_ty_ty.

    eapply type_heq_sym in H3'; eauto using validity_ty_ty, type_hetero_to_homo, typing.
    destruct H4'.
    eapply type_heq_trans' in  H12. 5:eapply H3'. all:eauto using typing, type_hetero_to_homo, validity_ty_ty.
    destruct H12.

    eapply tr_eq_conclude. 7:eapply H12.
    all:eauto using decoration, typing, type_hetero_to_homo, validity_ty_ty.
    

  - intros * ? ihA ? ihB ? iht ? ihu ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    specialize iht with (1 := hca).
    eapply change_type in iht. 2: eassumption.
    specialize ihu with (1 := hc).
    eapply change_type in ihu. 2: eassumption.
    destruct ihu as (u' & ihu).
    destruct iht as (t' & iht).
    destruct ihA as (? & ? & _), ihB as (? & ? & _), iht as (? & ? & _).
    destruct ihu as (? & ? & _).
    eapply tr_eq_conclude_by_refl.
    4:eapply conv_beta.
    all:eauto using decoration, substs_decs_one.

  - intros * ? ihA ? ihB ? iht ? ihu * ? iheq * hc.
    destruct j. 2:econstructor.

    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as (A' & ihA).
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    specialize ihB with (1 := hca). eapply keep_sort in ihB.
    destruct ihB as (B' & ihB).
    destruct ihA as (? & ? & _), ihB as (? & ? & _).
    specialize iht with (1 := hc).
    eapply tr_tm_get in iht. 2:econstructor;eauto. 2:eauto using typing.
    specialize ihu with (1 := hc). 
    eapply tr_tm_get in ihu. 2:econstructor;eauto. 2:eauto using typing.
    destruct iht as (t' & ? & ?).
    destruct ihu as (u' & ? & ?).

    specialize iheq with (1 := hca).
    eapply tr_eq_ty_sgeth in iheq; eauto.
    destruct iheq.

    eassert (Γ' ,, (i, A') ⊢p< _ > app _ _ (S ⋅ A') (up_ren S ⋅ B') (S ⋅ t') (var 0) : _).
    { eapply type_app. 3:eapply type_ren. 3:eapply H4.
      5:rasimpl;reflexivity.
      1,2:eapply type_ren. 
      all: eauto using WellRen_S, WellRen_up, ctx_typing, validity_ty_ctx, type_ren.
      econstructor. 2:econstructor. eauto using ctx_typing, validity_ty_ctx. } 
    eassert (Γ' ,, (i, A') ⊢p< _ > app _ _ (S ⋅ A') (up_ren S ⋅ B') (S ⋅ u') (var 0) : _).
    { eapply type_app. 3:eapply type_ren. 3:eapply H6.
      5:rasimpl;reflexivity.
      1,2:eapply type_ren. 
      all: eauto using WellRen_S, WellRen_up, ctx_typing, validity_ty_ctx, type_ren.
      econstructor. 2:econstructor. eauto using ctx_typing, validity_ty_ctx. }

      
   
    assert (t'0 ~ app i (ty n) (S ⋅ A') (up_ren S ⋅ B') (S ⋅ t') (var 0)).
    { unfold t_app_x in H7.  
      eapply dec_to_sim in H7. eapply sim_sym in H7. eapply sim_trans; eauto.
      econstructor. 4:econstructor. all: eauto using rename_dec, dec_to_sim. }
    assert (u'0 ~ app i (ty n) (S ⋅ A') (up_ren S ⋅ B') (S ⋅ u') (var 0)).
    { unfold u_app_x in H8. 
      eapply dec_to_sim in H8. eapply sim_sym in H8. eapply sim_trans; eauto.
      econstructor. 4:econstructor. all: eauto using rename_dec, dec_to_sim. }

    eapply sim_heq_same_ctx in H14; eauto.
    eapply sim_heq_same_ctx in H15; eauto.
    destruct H14, H15.
    eapply type_heq_trans in H15. 5:eapply H11. all:eauto.
    eapply type_heq_sym in H14;eauto. eapply type_heq_trans in H15. 5:eapply H14. all:eauto.
    rasimpl in H15. rewrite subst_id_reduce1 in H15. rasimpl in H15.

    eapply type_heq_funext in H15; eauto.


    
    eapply tr_eq_conclude.  7:eapply H15.
    all:eauto using decoration.



  (* case natrec_zero *)
  - intros * ? ihP ? ihz ? ihs ?  hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _). 
    eassert (Γ' ⊢p< l > rec l P' z' s' zero ≡ z' : _) by eauto using conversion.
    eapply tr_eq_conclude_by_refl. 4:eapply H5.
    all:eauto using decoration, substs_decs_two, substs_decs_one.

  (* case natrec_succ *)
  - intros * ? ihP ? ihz ? ihs ? iht ? hc.
    eapply tr_ctx_cons with (i := ty 0) in hc as hcn.
    2:{ eapply tr_Nat. eassumption. }
    specialize ihP with (1 := hcn).
    eapply keep_sort in ihP. destruct ihP as (P' & ihP).
    specialize ihz with (1 := hc).
    eapply change_type in ihz.
    2:{ eapply tr_substitution_one_sort. all: eauto using tr_zero_full. }
    destruct ihz as (?z' & ihz).
    eapply tr_ctx_cons in hcn as hcns. 2: eassumption.
    specialize ihs with (1 := hcns).
    eapply change_type in ihs.
    2:{
      eapply tr_substitution_sort. 1,2: eassumption.
      eapply autosubst_simpl_tr_subst_data. 1: exact _. 1: repeat constructor.
      eapply tr_subst_scons with (A := Nat).
      2:{
        cbn. eapply tr_succ_full.
        eapply tr_var_known. 3: eassumption.
        - eapply BasicMetaTheory.varty_meta.
          { repeat econstructor. }
          reflexivity.
        - eapply varty_meta.
          { repeat econstructor. }
          reflexivity.
      }
      eapply tr_subst_ren. 1: eassumption.
      eapply WellRen_comp. all: eapply WellRen_S.
    }
    destruct ihs as (?s' & ihs).
    specialize iht with (1 := hc).
    eapply change_type in iht. 2:{ eapply tr_Nat. eassumption. }
    destruct iht as (?t' & iht).
    destruct
      ihP as (? & ? & _),
      ihz as (? & ? & _),
      ihs as (? & ? & _),
      iht as (? & ? & _).
    assert (Γ' ⊢p< l > rec l P' z' s' (succ t') ≡ s' <[ rec l P' z' s' t' .: t'..] : P' <[ (succ t')..]) by eauto using conversion.
    eapply tr_eq_conclude_by_refl. 4:eapply H7.
    all:eauto using decoration, substs_decs_two, substs_decs_one.
  - intros ?? l * ? ? ihA ? ihR ? ihP. cbn zeta. intros ? ihp ? iha ? ihq ? hc.
    specialize ihA with (1 := hc). eapply keep_sort in ihA.
    destruct ihA as [A' ihA].
    eapply tr_ctx_cons in hc as hca. 2: eassumption.
    eapply tr_ctx_cons in hca as hcaa.
    2:{ eapply tr_rename_sort. 1,2: eauto. eapply WellRen_S. }
    specialize ihR with (1 := hcaa). eapply keep_sort in ihR.
    destruct ihR as [R' ihR].
    specialize ihP with (1 := hca). eapply keep_sort in ihP.
    destruct ihP as [P' ihP].
    specialize iha with (1 := hc).
    eapply change_type in iha. 2: eassumption.
    destruct iha as [a' iha].
    lazymatch type of ihp with
    | ∀ G', tr_ctx ?G G' → _ => eassert (hcap : tr_ctx G _)
    end.
    { eapply tr_ctx_cons. 1: eassumption.
      eapply tr_Pi.
      - eapply tr_rename_sort. 1,2: eassumption.
        apply WellRen_S.
      - eapply tr_meta.
        { eapply tr_Pi.
          - eapply tr_rename_sort. 1,2: eassumption.
            apply well_rcons_alt. 1: apply well_rcons_alt.
            + apply WellRen_weak. apply WellRen_S.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
            + eapply varty_meta.
              { repeat constructor. }
              rasimpl. reflexivity.
          - eapply tr_rename_sort. 1: eassumption.
            + eapply tr_ctx_cons. 1: eassumption.
              eapply tr_rename_sort. 1,2: eassumption.
              apply well_rcons_alt. 1: apply well_rcons_alt.
              * apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
            + apply well_rcons_alt.
              * do 2 apply WellRen_weak. apply WellRen_S.
              * eapply varty_meta.
                { repeat constructor. }
                rasimpl. reflexivity.
        }
        all: destruct l ; reflexivity.
    }
    specialize ihp with (1 := hcap).
    eapply change_type in ihp.
    2:{
      eapply tr_rename_sort. 1,2: eassumption.
      apply well_rcons_alt.
      - apply WellRen_weak. apply WellRen_S.
      - eapply varty_meta.
        { repeat constructor. }
        rasimpl. reflexivity.
    }
    destruct ihp as [p' ihp].
    specialize ihq with (1 := hc).
    eapply change_type in ihq. 2:{ eapply tr_acc. all: eauto. }
    destruct ihq as [q' ihq].
    destruct ihA, ihR, ihP, iha, ihp, ihq.
    intuition eauto.
    eassert (_ ⊢p< _ > _ : obseq _ _ (accel (ty n) (ty l) A' R' P' p' a' q') _) by eauto using typing.
    eapply validity_ty_ty in H10 as H'. eapply type_inv in H'. dependent destruction H'.
    eapply type_homo_to_hetero in H10; eauto.
    eapply tr_eq_conclude.
    7:eapply H10.
    all:eauto 10 using decoration, substs_decs_one, substs_decs_two, rename_dec.
    eapply substs_decs_two.
    all:eauto.
    econstructor; eauto.
    1,2:econstructor; eauto.
    3:econstructor. 8:econstructor.
    all:eauto using decoration, rename_dec.
    all:setoid_rewrite subst_id_reduce1.
    1,2:eapply substs_decs_one; eauto using rename_dec.
  
    (* case sym *)
  - intros. destruct l. 2:econstructor.
    eapply H in H0.
    dependent destruction H0.
    eapply type_heq_sym in H5; eauto using validity_ty_ty.
    
    eapply tr_eq_conclude. 7:eapply H5.
    all:eauto.

  (* case trans *)
  - intros. destruct l. 2:econstructor.
    eapply H in H1 as h. eapply H0 in H1 as h0.
    clear H H0.
    dependent destruction h.
    eapply tr_eq_ty_geth in h0.
    5:eauto using validity_ty_ty.
    all:eauto using validity_ty_ty, type_heq_refl.
    dependent destruction h0.

    rename t'0 into u''. rename u'0 into v'.

    assert (u' ~ u'') by eauto using dec_to_sim, sim_sym, sim_trans.
    eapply sim_heq_same_ctx in H11; eauto.
    destruct H11.

    eapply type_heq_trans in H11. 5:eapply H5. all:eauto.
    eapply type_heq_trans in H10. 5:eapply H11. all:eauto.

    eapply tr_eq_conclude.
    7:eapply H10.
    all:eauto.
Qed.

Lemma conservativity e l A :
  ∙ ⊢p< Ax l > A : Sort l  ->
  ∙ ⊢d< l > e : A ->
  exists e', ∙ ⊢p< l > e' : A.
Proof.
  intros Hty HA.
  eapply typing_conversion_trans in HA.
  2: repeat econstructor.
  destruct HA as [A' [e' [HA [Hincl Hincl']]]].
  assert (HA' : ∙ ⊢p< Ax l > A' : Sort l) by now eapply validity_ty_ty in HA.
  eapply dec_to_sim, sim_sym in Hincl'.
  eapply sim_heq_same_ctx in Hincl'; eauto.
  destruct Hincl'.
  eapply type_hetero_to_homo in H; eauto.
  eapply type_cast in HA; eauto.
Qed.


Lemma type_mk_Nat k : ∙ ⊢p< ty 0 > mk_Nat k : Nat.
Proof.
  induction k; simpl.
  - eapply type_zero; econstructor.
  - eapply type_succ; eauto. 
Qed. 


Theorem prop_canonicity n : 
    ∙ ⊢p< ty 0 > n : Nat ->
    exists k e, eval (erasure n) k /\ 
    ∙ ⊢p< prop > e : obseq (ty 0) Nat n (mk_Nat k) /\
    (forall k', eval (erasure n) k' -> k = k').
Proof.
  intros. eapply p_in_d in H as H'.
  
  eapply computational_canonicity in H' as (k & ? & H' & ?).
  exists k.  
  eassert (∙ ⊢d< _ > _ : obseq (ty 0) Nat n (mk_Nat k)) as Hcan.
  1:eapply type_conv.
  1:eapply type_obsrefl.
  3:econstructor.
  5:eauto.
  all:eauto using typing, validity_conv_left, conv_refl, validity_ty_ctx.
  eapply conservativity in Hcan; eauto using typing, type_mk_Nat, ctx_typing. destruct Hcan.
  eexists. split. 2:split. all:eassumption.
Qed.
