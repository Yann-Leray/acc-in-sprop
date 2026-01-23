
From Stdlib Require Import Utf8 List Arith Bool Lia.
From AccInSProp Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl Util BasicAST Typing. 
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope.


Derive Signature for varty.
Derive Signature for ctx_typing.
Derive Signature for typing.
Derive Signature for ConvCtx.
Derive Signature for WellSubst.
Derive Signature for WellRen.
Derive Signature for ConvSubst.
Derive NoConfusion for term.
Derive NoConfusion for level.


Lemma p_in_d :
  (forall Γ l t A, 
    Γ ⊢p< l > t : A -> Γ ⊢d< l > t : A
  ) /\ 
  (forall Γ l t u A, 
    Γ ⊢p< l > t ≡ u : A -> Γ ⊢d< l > t ≡ u : A
  ) /\
  (forall Γ, ⊢p Γ -> ⊢d Γ).
Proof.
  eapply type_conv_ctx_mut; eauto 6 using typing, conversion, ctx_typing.
Qed.

Lemma varty_unique Γ l x A B :
  Γ ∋< l > x : A →
  Γ ∋< l > x : B →
  A = B.
Proof.
  intros hA hB.
  induction hA in B, hB |- *.
  - inversion hB. reflexivity.
  - inversion hB. subst. firstorder congruence.
Qed.

Lemma Ax_inj l l' : Ax l = Ax l' → l = l'.
Proof.
  intro H. destruct l; destruct l'; inversion H; auto.
Qed.

(** Typing implies scoping *)

Lemma varty_scoped Γ l x A :
  Γ ∋< l > x : A →
  scoped (length Γ) (var x) = true.
Proof.
  induction 1.
  - reflexivity.
  - cbn - ["<?"] in *. rewrite Nat.ltb_lt in *. lia.
Qed.

Lemma typing_scoped M Γ l t A :
  Γ ▹ M ⊢< l > t : A →
  scoped (length Γ) t = true.
Proof.
  induction 1.
  all: try solve [ intros ; cbn - ["<?"] in * ; eauto using varty_scoped ].
  all: solve [
    intros ;
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    intuition eauto
  ].
Qed.

Lemma typing_closed M l t A :
  ∙ ▹ M ⊢< l > t : A →
  closed t = true.
Proof.
  intros h.
  eapply typing_scoped with (Γ := ∙).
  eassumption.
Qed.

Lemma scoped_ren ρ k t :
  scoped k t = true →
  (Nat.iter k up_ren ρ) ⋅ t = t.
Proof.
  intros h.
  induction t in k, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    repeat change (upRen_term_term (Nat.iter ?k up_ren ?ρ)) with (Nat.iter (S k) up_ren ρ) ;
    intuition (f_equal ; eauto)
  ].
  cbn - ["<?"] in *. f_equal.
  apply Nat.ltb_lt in h.
  induction n as [| n ih] in k, h |- *.
  - destruct k. 1: lia.
    reflexivity.
  - destruct k. 1: lia.
    cbn. unfold ">>". f_equal.
    apply ih. lia.
Qed.

Corollary closed_ren ρ t :
  closed t = true →
  ρ ⋅ t = t.
Proof.
  intros h.
  eapply scoped_ren in h. eauto.
Qed.

Lemma conv_refl M Γ t l A :
  Γ ▹ M ⊢< l > t : A →
  Γ ▹ M ⊢< l > t ≡ t : A.
Proof.
  induction 1.
  all: solve [ econstructor ; eauto ].
Qed.

Lemma conv_refl_conv M Γ u v l A :
  Γ ▹ M ⊢< l > u ≡ v : A →
  Γ ▹ M ⊢< l > u ≡ u : A.
Proof.
  intros h.
  eapply conv_trans. 1: eassumption.
  apply conv_sym. assumption.
Qed.

Theorem refl_subst M Γ σ Δ :
  Γ ▹ M ⊢s σ : Δ →
  Γ ▹ M ⊢s σ ≡ σ : Δ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + apply conv_refl. assumption.
Qed.

Lemma varty_meta Γ l x A B :
  Γ ∋< l > x : A →
  A = B →
  Γ ∋< l > x : B.
Proof.
  intros h ->. exact h.
Qed.

Lemma WellRen_meta Γ Γ' Δ Δ' ρ :
  Γ ⊢r ρ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ⊢r ρ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

#[export] Instance WellRen_morphism :
  Proper (eq ==> (`=1`) ==> eq ==> iff) WellRen.
Proof.
  intros Γ ? <- ρ ρ' e Δ ? <-.
  revert ρ ρ' e. wlog_iff. intros ρ ρ' e h.
  induction h as [| ρ Δ l A h ih ho] in ρ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellRen :
  ∀ Γ Δ r s,
    RenSimplification r s →
    Γ ⊢r r : Δ ↔ Γ ⊢r s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellRen_morphism. 1,3: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellRen : rasimpl_outermost.

Lemma WellRen_weak Γ Δ ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ,, (l, A) ⊢r (ρ >> S) : Δ.
Proof.
  induction 1 as [| ρ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply varty_meta.
      * unfold ">>". constructor. eassumption.
      * rasimpl. reflexivity.
Qed.

Lemma WellRen_up Γ Δ l A A' ρ :
  Γ ⊢r ρ : Δ →
  A' = ρ ⋅ A →
  Γ ,, (l, A') ⊢r up_ren ρ : Δ ,, (l, A).
Proof.
  intros h p. subst.
  constructor.
  - rasimpl. apply WellRen_weak. assumption.
  - rasimpl. cbn. eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Lemma varty_ren Γ Δ ρ x l A :
  Γ ∋< l > x : A →
  Δ ⊢r ρ : Γ →
  Δ ∋< l > ρ x : ρ ⋅ A.
Proof.
  intros hx hr.
  induction hr as [| ρ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellRen_comp Γ Δ Θ ρ ρ' :
  Δ ⊢r ρ : Θ →
  Γ ⊢r ρ' : Δ →
  Γ ⊢r (ρ >> ρ') : Θ.
Proof.
  intros hρ hρ'.
  induction hρ as [| ρ Θ i B h ih ho] in ρ', Γ, hρ' |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". eapply varty_meta.
      1: eauto using varty_ren.
      rasimpl. reflexivity.
Qed.

Lemma WellRen_id Γ :
  Γ ⊢r id : Γ.
Proof.
  induction Γ as [| [l A] Γ ih].
  - constructor.
  - constructor.
    + change (S >> id) with (id >> S).
      eauto using WellRen_weak.
    + constructor.
Qed.

Lemma WellRen_S Γ l A :
  Γ ,, (l, A) ⊢r S : Γ.
Proof.
  change S with (id >> S).
  apply WellRen_weak.
  apply WellRen_id.
Qed.

Lemma meta_conv M Γ t l A B :
  Γ ▹ M ⊢< l > t : A →
  A = B →
  Γ ▹ M ⊢< l > t : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_lvl Γ t A i j M :
  Γ ▹ M ⊢< i > t : A →
  i = j →
  Γ ▹ M ⊢< j > t : A.
Proof.
  intros ? ->. assumption.
Qed.

Lemma meta_conv_conv Γ u v l A B M :
  Γ ▹ M ⊢< l > u ≡ v : A →
  A = B →
  Γ ▹ M ⊢< l > u ≡ v : B.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_lvl_conv Γ u v l l' A M :
  Γ ▹ M ⊢< l > u ≡ v : A →
  l = l' →
  Γ ▹ M ⊢< l' > u ≡ v : A.
Proof.
  intros ? ->. auto.
Qed.

Lemma meta_rhs_conv Γ u v w l A M :
  Γ ▹ M ⊢< l > u ≡ v : A →
  v = w →
  Γ ▹ M ⊢< l > u ≡ w : A.
Proof.
  intros ? ->. auto.
Qed.

Lemma validity_ctx M :
  (∀ Γ l t A,
    Γ ▹ M ⊢< l > t : A →
    ▹ M ⊢ Γ
  ) ∧
  (∀ Γ l u v A,
    Γ ▹ M ⊢< l > u ≡ v : A →
    ▹ M ⊢ Γ).
Proof.
  apply typing_mutind. all: eauto.
Qed.

Corollary validity_ty_ctx M Γ l t A :
  Γ ▹ M ⊢< l > t : A →
  ▹ M ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.

Corollary validity_conv_ctx M Γ l t u A :
  Γ ▹ M ⊢< l > t ≡ u : A →
  ▹ M ⊢ Γ.
Proof.
  intros. eapply validity_ctx in H; eauto.
Qed.

Lemma thread_pi M Γ i j A B :
  Γ ▹ M ⊢< Ax i > A : Sort i →
  (▹ M ⊢ Γ ,, (i, A) → Γ ,, (i, A) ▹ M ⊢< Ax j > B : Sort j) →
  Γ ▹ M ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j).
Proof.
  intros.
  firstorder eauto using type_pi, ctx_cons, validity_ty_ctx.
Qed.

Lemma well_rcons_alt Γ Δ x ρ l A :
  Γ ⊢r ρ : Δ →
  Γ ∋< l > x : ρ ⋅ A →
  Γ ⊢r (x .: ρ) : Δ ,, (l , A).
Proof.
  intros hr hx.
  constructor.
  - erewrite autosubst_simpl_WellRen. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma varty0_eq Γ l A B :
  S ⋅ A = B →
  Γ ,, (l , A) ∋< l > 0 : B.
Proof.
  intros <-.
  constructor.
Qed.

Lemma vartyS_eq Γ i j A B C x :
  Γ ∋< i > x : A →
  S ⋅ A = C →
  Γ ,, (j, B) ∋< i > S x : C.
Proof.
  intros h <-.
  constructor. assumption.
Qed.

Ltac meta_conv :=
  lazymatch goal with
  | |- _ ▹ _ ⊢< _ > _ : _ => eapply meta_conv
  | |- _ ▹ _ ⊢< _ > _ ≡ _ : _ => eapply meta_conv_conv
  end.

Ltac subst_def :=
  lazymatch goal with
  | u := _ |- _ => subst u
  end.

Create HintDb sidecond.

Hint Resolve
  WellRen_up WellRen_comp WellRen_S well_rcons_alt varty0_eq vartyS_eq
  ctx_nil ctx_cons
  : sidecond.

Hint Extern 100 (_ = _) =>
  rasimpl ; reflexivity : sidecond.

Hint Extern 1000 (_ = _) =>
  repeat subst_def ; rasimpl ; reflexivity : sidecond.

Ltac ren_ih :=
  lazymatch goal with
  | |- _ ▹ _ ⊢< _ > _ ⋅ _ ⋅ _ : _ => rasimpl ; ren_ih
  | ih : ∀ (Δ : ctx) (ρ : nat → nat), ▹ _ ⊢ Δ → Δ ⊢r ρ : ?Γ → Δ ▹ _ ⊢< _ > ρ ⋅ ?t : _ |- _ ▹ _ ⊢< _ > ?r ⋅ ?t : _ =>
    eapply meta_conv ; [
      eapply ih with (ρ := r) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        ren_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | ih : ∀ (Δ : ctx) (ρ : nat → nat), ▹ _ ⊢ Δ → Δ ⊢r ρ : _ → Δ ▹ _ ⊢< _ > ρ ⋅ ?u ≡ ρ ⋅ ?v : _ |- _ ▹ _ ⊢< _ > ?r ⋅ ?u ≡ _ ⋅ ?v : _ =>
    eapply meta_conv_conv ; [
      eapply ih with (ρ := r) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        ren_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | |- _ => eauto with sidecond
  end.

Ltac typing_ren_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    econstructor ;
    ren_ih
  | eauto with sidecond
  ].

Ltac comp_rule :=
  first [
    eapply conv_cast_refl
  | eapply conv_cast_pi
  | eapply conv_beta
  | eapply conv_rec_zero
  | eapply conv_rec_succ
  | eapply conv_accel_accin
  ].

Ltac typing_ren_comp_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    eapply meta_rhs_conv ; [
      comp_rule ;
      ren_ih
    | eauto with sidecond
    ]
  | eauto with sidecond
  ].

Lemma typing_conversion_ren M :
  (∀ Γ l t A,
    Γ ▹ M ⊢< l > t : A →
    ∀ Δ ρ,
      ▹ M ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ▹ M ⊢< l > ρ ⋅ t : ρ ⋅ A
  ) ∧
  (∀ Γ l u v A,
    Γ ▹ M ⊢< l > u ≡ v : A →
    ∀ Δ ρ,
      ▹ M ⊢ Δ →
      Δ ⊢r ρ : Γ →
      Δ ▹ M ⊢< l > ρ ⋅ u ≡ ρ ⋅ v : ρ ⋅ A).
Proof.
  apply typing_mutind.
  1, 23: solve [ intro ; cbn ; econstructor ; eauto using varty_ren ].
  all: try solve [
    intros ; try econstructor ; eauto with sidecond
  ].
  all: try solve [ typing_ren_tac ].
  all: try solve [ typing_ren_comp_tac ].
  - intros. cbn in *. rewrite closed_ren.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_ren_tac.
    econstructor. 1: ren_ih.
    meta_conv. 1: eapply meta_lvl.
    { rasimpl. econstructor.
      all: ren_ih.
      - eauto 6 with sidecond.
      - eauto 6 with sidecond.
      - eauto 7 with sidecond.
    }
    all: destruct l. all: reflexivity.
  - intros. simpl. eapply meta_conv.
    + eapply type_accelcomp; eauto with sidecond.
      all:ren_ih.
      econstructor.
      2:eapply meta_conv. 2:eapply meta_lvl.
      2:econstructor.
      1-3:ren_ih.
      * econstructor. 1:econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor.
        2:eapply varty_meta. 2:econstructor. 2:econstructor.
        all:rasimpl;reflexivity.
      * econstructor. 1:econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor.
        2:eapply varty_meta. 2:econstructor. 2:econstructor.
        all:rasimpl;reflexivity.
      * econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor. 1:econstructor.
        all:rasimpl;reflexivity.
      * reflexivity.
      * reflexivity.
    + rasimpl. f_equal. f_equal. unfold t10, t9, t8, t7, t6, t5, Awk, Rwk, Pwk, pwk,P'', B, P', R'.
      simpl. f_equal. f_equal. 1:ssimpl ; reflexivity.
      f_equal; rasimpl. 1-2:reflexivity.
      f_equal.    
  - intros. cbn in *. rewrite closed_ren.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_ren_tac.
    econstructor. 1: ren_ih.
    meta_conv. 1: eapply meta_lvl.
    { econstructor. all: ren_ih.
      - eauto 6 with sidecond.
      - eauto 6 with sidecond.
      - eauto 7 with sidecond.
    }
    all: destruct l ; reflexivity.
  - intros. simpl. eapply meta_conv_conv.
    + eapply conv_accelcomp; eauto with sidecond.
      all:ren_ih.
      econstructor.
      2:eapply meta_conv. 2:eapply meta_lvl.
      2:econstructor.
      1-3:ren_ih.
      * econstructor. 1:econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor.
        2:eapply varty_meta. 2:econstructor. 2:econstructor.
        all:rasimpl;reflexivity.
      * econstructor. 1:econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor.
        2:eapply varty_meta. 2:econstructor. 2:econstructor.
        all:rasimpl;reflexivity.
      * econstructor.
        all:ssimpl. 1:eauto using WellRen_weak.
        1:eapply varty_meta. 1:econstructor. 1:econstructor.
        all:rasimpl;reflexivity.
      * reflexivity.
      * reflexivity.
    + rasimpl. f_equal. f_equal. unfold t7, t6, t5, t4, t3, t2, Awk, Rwk, Pwk, pwk,P'', B, P_, R_.
      simpl. f_equal. f_equal. 1:ssimpl ; reflexivity.
      f_equal; rasimpl. 1-2:reflexivity.
      f_equal.    
  - typing_ren_comp_tac.
    repeat subst_def. rasimpl. f_equal. f_equal. f_equal. f_equal. f_equal.
    all: rasimpl. 1,2: reflexivity.
    f_equal.
    all: substify.
    all: apply ext_term.
    all: intros []. all: reflexivity.
  - (* eta *)
    intros ?????????????????? ih ? ρ **. cbn in *.
    eapply conv_eta. 3,4: ren_ih. 1,2: ren_ih. rasimpl. rasimpl in ih.
    eapply (ih _ (0 .: (ρ >> S))).
    1: econstructor; eauto.
    eauto with sidecond.
  - typing_ren_comp_tac.
    + rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: try reflexivity.
      all: substify. all: apply ext_term. all: intros [| []]. all: reflexivity.
    + rasimpl. apply ext_term. intros [].
    all: cbn. all: rasimpl. all: reflexivity.
  - typing_ren_comp_tac.
    + econstructor. 1: ren_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor. all: ren_ih.
        - eauto 6 with sidecond.
        - eauto 6 with sidecond.
        - eauto 7 with sidecond.
      }
      all: reflexivity.
    + repeat subst_def. rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: try reflexivity.
      all: f_equal.
      1,2: substify. 1,2: apply ext_term. 1,2: intros [] ; reflexivity.
      f_equal. 1-3: substify. 1-3: apply ext_term.
      1-3: intros [| []] ; reflexivity.
      f_equal. substify. apply ext_term. intros [| []] ; reflexivity.
Qed.

Lemma type_ren M Γ l t A Δ ρ A' :
  Γ ▹ M ⊢< l > t : A →
  ▹ M ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A →
  Δ ▹ M ⊢< l > ρ ⋅ t : A'.
Proof.
  intros h **. subst. eapply typing_conversion_ren in h. all: eauto.
Qed.

Lemma conv_ren M Γ l t u A Δ ρ A' :
  Γ ▹ M ⊢< l > t ≡ u : A →
  ▹ M ⊢ Δ →
  Δ ⊢r ρ : Γ →
  A' = ρ ⋅ A →
  Δ ▹ M ⊢< l > ρ ⋅ t ≡ ρ ⋅ u : A'.
Proof.
  intros h **. subst. eapply typing_conversion_ren in h ; eauto.
Qed.

Lemma ups_below k σ n :
  n < k →
  Nat.iter k up_term σ n = var n.
Proof.
  intro h.
  induction k as [| k ih] in n, σ, h |- *. 1: lia.
  cbn. destruct n as [| ].
  - reflexivity.
  - cbn. unfold ">>". unfold Nat.iter in ih. rewrite ih. 2: lia.
    reflexivity.
Qed.

Lemma scoped_subst σ k t :
  scoped k t = true →
  t <[ Nat.iter k up_term σ ] = t.
Proof.
  intros h.
  induction t in k, σ, h |- *.
  all: try solve [ cbn ; eauto ].
  all: try solve [
    cbn in * ;
    rewrite ?Bool.andb_true_iff in * ;
    repeat change (up_term_term (Nat.iter ?k up_term ?σ)) with (Nat.iter (S k) up_term σ) ;
    intuition (f_equal ; eauto)
  ].
  cbn - ["<?"] in *.
  apply ups_below.
  apply Nat.ltb_lt. assumption.
Qed.

Corollary closed_subst σ t :
  closed t = true →
  t <[ σ ] = t.
Proof.
  intros h.
  eapply scoped_subst in h. eauto.
Qed.

#[export] Instance WellSubst_morphism M :
  Proper (eq ==> eq ==> (`=1`) ==> iff) (WellSubst M).
Proof.
  intros Γ ? <- Δ ? <- σ σ' e.
  revert σ σ' e. wlog_iff. intros σ σ' e h.
  induction h as [| σ Δ l A h ih ho] in σ', e |- *.
  - constructor.
  - constructor.
    + eapply ih. intros x. unfold ">>". apply e.
    + rewrite <- e. assumption.
Qed.

Lemma autosubst_simpl_WellSubst M :
  ∀ Γ Δ r s,
    SubstSimplification r s →
    Γ ▹ M ⊢s r : Δ ↔ Γ ▹ M ⊢s s : Δ.
Proof.
  intros Γ Δ r s H.
  apply WellSubst_morphism. 1,2: auto.
  apply H.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_WellSubst : rasimpl_outermost.

Lemma well_scons_alt M Γ Δ σ u l A :
  Γ ▹ M ⊢s σ : Δ →
  Γ ▹ M ⊢< l > u : A <[ σ ] →
  Γ ▹ M ⊢s (u .: σ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_WellSubst. 2: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma WellSubst_weak M  Γ Δ σ l A :
  Γ ▹ M ⊢s σ : Δ →
  Γ ▹ M ⊢< Ax l > A : Sort l →
  Γ ,, (l, A) ▹ M ⊢s (σ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.

Lemma WellSubst_weak_two M Γ Δ σ l A l' B :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Γ ,, (l, A) ,, (l', B) →
  Γ ,, (l, A) ,, (l', B) ▹ M ⊢s (σ >> ren_term (S >> S)) : Δ.
Proof.
  intros.
  intros.  induction H.
  - econstructor.
  - econstructor. 1:ssimpl.  1: asimpl in IHWellSubst; eauto.
    ssimpl. eapply typing_conversion_ren in H1.
    1:eapply meta_conv. 1:eassumption.
    1:rasimpl; reflexivity.
    1:eauto.
    1: eapply WellRen_weak. eapply WellRen_S.
Qed.


Lemma WellSubst_weak_three M Γ Δ σ l A l' B l'' C :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Γ ,, (l, A) ,, (l', B) ,, (l'', C) →
  Γ ,, (l, A) ,, (l', B) ,, (l'', C) ▹ M ⊢s (σ >> ren_term (S >> S >> S)) : Δ.
Proof.
  intros.  induction H.
  - econstructor.
  - econstructor. 1:ssimpl.  1: asimpl in IHWellSubst; eauto.
    ssimpl. eapply typing_conversion_ren in H1.
    1:eapply meta_conv. 1:eassumption.
    1:rasimpl; reflexivity.
    1:eauto.
    1: eapply WellRen_weak. 1:eapply WellRen_weak. eapply WellRen_S.
Qed.

Lemma WellSubst_up M Γ Δ l A A' σ :
  Γ ▹ M ⊢s σ : Δ →
  A' = A <[ σ ] →
  Γ ▹ M ⊢< Ax l > A <[ σ ] : Sort l →
  Γ ,, (l, A') ▹ M ⊢s up_term σ : Δ ,, (l, A).
Proof.
  intros. subst.
  constructor.
  - rasimpl. apply WellSubst_weak; assumption.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
   eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.


Lemma WellSubst_up_two M Γ Δ σ l l' B A A' B' :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  A' = A <[ σ ] -> B' = B <[ up_term σ ] ->
  Γ ,, (l, A') ,, (l', B') ▹ M ⊢s up_term (up_term σ) : Δ ,, (l, A) ,, (l', B).
Proof.
  intros. subst. dependent destruction H0.
  dependent destruction H0.
  econstructor. 1:econstructor.
  - rasimpl. eapply WellSubst_weak. 1:eapply WellSubst_weak.
    all:eauto.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor. constructor.
    + rasimpl. reflexivity.
  - rasimpl. cbn. econstructor.
    1: econstructor; eauto using validity_ty_ctx.
     eapply varty_meta.
    + constructor.
    + rasimpl. reflexivity.
Qed.

Lemma varty_subst M Γ Δ σ x l A :
  Γ ∋< l > x : A →
  Δ ▹ M ⊢s σ : Γ →
  Δ ▹ M ⊢< l > σ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma WellSubst_meta M Γ Γ' Δ Δ' σ :
  Γ ▹ M ⊢s σ : Δ →
  Γ = Γ' →
  Δ = Δ' →
  Γ' ▹ M ⊢s σ : Δ'.
Proof.
  intros ? -> ->. auto.
Qed.

Lemma WellSubst_ren M Γ Δ ρ :
  Δ ⊢r ρ : Γ →
  ▹ M ⊢ Δ →
  Δ ▹ M ⊢s (ρ >> var) : Γ.
Proof.
  induction 1.
  - constructor.
  - constructor.
    + eauto.
    + rasimpl. unfold ">>".
      econstructor. all: eassumption.
Qed.

Lemma WellSubst_compr M Γ Δ Θ σ ρ :
  Δ ▹ M ⊢s σ : Θ →
  Γ ⊢r ρ : Δ →
  ▹ M ⊢ Γ →
  Γ ▹ M ⊢s (σ >> ren_term ρ) : Θ.
Proof.
  intros hσ hρ hΓ.
  induction hσ as [| σ Θ i B h ih ho] in ρ, Γ, hΓ, hρ |- *.
  - constructor.
  - constructor.
    + eauto.
    + unfold ">>". meta_conv.
      { eapply type_ren. all: eauto. }
      rasimpl. reflexivity.
Qed.

Hint Resolve
  WellSubst_up WellSubst_weak well_scons_alt WellSubst_ren WellSubst_compr
  : sidecond.

Ltac subst_ih :=
  lazymatch goal with
  | |- _ ▹ _ ⊢< _ > _ ⋅ _ ⋅ _ : _ => rasimpl ; subst_ih
  | ih : ∀ (Δ : ctx) (σ : nat → term), ▹ _ ⊢ Δ → Δ ▹ _ ⊢s σ : _ → Δ ▹ _ ⊢< _ > ?t <[ σ ] : _ |- _ ▹ _ ⊢< _ > ?t <[ ?s ] : _ =>
    eapply meta_conv ; [
      eapply ih with (σ := s) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        subst_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | ih : ∀ (Δ : ctx) (σ : nat → term), ▹ _ ⊢ Δ → Δ ▹ _ ⊢s σ : _ → Δ ▹ _ ⊢< _ > ?u <[ σ ] ≡ ?v <[ σ ] : _ |- _ ▹ _ ⊢< _ > ?u <[ ?s ] ≡ ?v <[ _ ] : _ =>
    eapply meta_conv_conv ; [
      eapply ih with (σ := s) ; [
        repeat (eassumption + eapply ctx_nil + eapply ctx_cons + eapply type_nat) ;
        subst_ih
      | eauto with sidecond
      ]
    | eauto with sidecond
    ]
  | |- _ => eauto with sidecond
  end.

(* Would have been cool, but too slow *)
(* Hint Extern 2000 (⊢ _ ,, _) => econstructor ; [| subst_ih] : sidecond. *)

Ltac typing_subst_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    econstructor ;
    subst_ih
  | eauto with sidecond
  ].

Ltac typing_subst_comp_tac :=
  intros ; cbn in * ;
  meta_conv ; [
    eapply meta_rhs_conv ; [
      comp_rule ;
      subst_ih
    | eauto with sidecond
    ]
  | eauto with sidecond
  ].

(* A bit weird but well *)
Hint Resolve type_nat : sidecond.

Lemma typing_conversion_subst M :
  (∀ Γ l t A,
    Γ ▹ M ⊢< l > t : A →
    ∀ Δ σ,
      ▹ M ⊢ Δ →
      Δ ▹ M ⊢s σ : Γ →
      Δ ▹ M ⊢< l > t <[ σ ] : A <[ σ ]
  ) ∧
  (∀ Γ l u v A,
    Γ ▹ M ⊢< l > u ≡ v : A →
    ∀ Δ σ,
      ▹ M ⊢ Δ →
      Δ ▹ M ⊢s σ : Γ →
      Δ ▹ M ⊢< l > u <[ σ ] ≡ v <[ σ ] : A <[ σ ]).
Proof.
  apply typing_mutind.
  23:{ intros. cbn. apply conv_refl. eauto using varty_subst. }
  all: try solve [ intros ; try econstructor ; eauto with sidecond ].
  all: try solve [ typing_subst_tac ].
  all: try solve [ typing_subst_comp_tac ].
  - intros. cbn. eauto using varty_subst.
  - intros. cbn in *. rewrite closed_subst.
    2:{ eapply typing_closed. eassumption. }
    econstructor. all: eassumption.
  - typing_subst_tac.
    eapply WellSubst_up. 1,2: eauto with sidecond.
    subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + rasimpl. eapply well_scons_alt.
      * eapply autosubst_simpl_WellSubst. 1: exact _.
        eapply well_scons_alt.
        -- eapply WellSubst_weak. 1: eauto with sidecond. subst_ih.
        -- econstructor. 2: eauto with sidecond.
          constructor. 1: auto with sidecond.
          subst_ih.
      * econstructor. 2: eauto with sidecond.
        econstructor. 1: eauto with sidecond.
        subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn. rasimpl.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply autosubst_simpl_WellSubst. 1: exact _.
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. rasimpl.
      econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih. eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. 1,2: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn. rasimpl.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply autosubst_simpl_WellSubst. 1: exact _.
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. rasimpl.
      eapply meta_lvl.
      1:econstructor. 3:reflexivity. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih. eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: reflexivity.
      + rasimpl. f_equal. f_equal. unfold t10, t9, t8, t7, t6, t5, Awk, Rwk, Pwk, pwk,P'', B, P', R'.
      simpl. f_equal. f_equal. 1:ssimpl. 1:substify ; reflexivity.
      f_equal; rasimpl. 1-2:reflexivity.
      f_equal.
  - typing_subst_tac.
    symmetry. apply closed_subst.
    eapply typing_closed. eassumption.
  - typing_subst_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + econstructor. 1:{ rasimpl. subst_ih. }
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. cbn. rasimpl.
      econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: destruct l ; reflexivity.

  - typing_subst_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + econstructor. 1:{ rasimpl. subst_ih. }
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. cbn. rasimpl.
      eapply meta_lvl.
      1:econstructor. 3:reflexivity.
       1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - rasimpl. subst_ih.
          unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - rasimpl. subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            }
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: reflexivity.
      + rasimpl. f_equal. f_equal. unfold t7, t6, t5, t4, t3, t2, Awk, Rwk, Pwk, pwk,P'', B, P_, R_.
      simpl. f_equal. f_equal. 1:ssimpl ; substify; reflexivity.
      f_equal; rasimpl. 1-2:reflexivity.
      f_equal.      
  - typing_subst_comp_tac.
    repeat subst_def. cbn. rasimpl. f_equal. f_equal.
    f_equal. f_equal. f_equal. all: rasimpl. all: reflexivity.
  - (* eta *)
    intros ?????????????????? ih ? σ **. cbn in *.
    eapply conv_eta. 3,4: subst_ih. 1,2: subst_ih.
    rasimpl. rasimpl in ih.
    specialize ih with (σ := up_term_term σ).
    cbn in ih. rasimpl in ih.
    eapply ih.
    1: econstructor; eauto.
    eauto with sidecond.
  - typing_subst_comp_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_comp_tac.
    eapply WellSubst_up. all: eauto with sidecond.
    subst_ih.
  - typing_subst_comp_tac.
    + rasimpl. subst_ih.
    + eapply WellSubst_up. all: eauto with sidecond.
      rasimpl. subst_ih.
    + rasimpl. econstructor. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all: reflexivity.
    + eapply WellSubst_up. all: eauto with sidecond.
      repeat subst_def. cbn. rasimpl.
      eapply meta_lvl.  1:econstructor. 3:reflexivity. 1: subst_ih.
      meta_conv. 1: eapply meta_lvl.
      { econstructor.
        - subst_ih. unfold ">>". cbn.
          eapply autosubst_simpl_WellSubst. 1: exact _.
          eapply well_scons_alt.
          + eapply well_scons_alt.
            * eapply WellSubst_compr. all: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + econstructor. 2: eauto with sidecond.
            econstructor. 1: eauto with sidecond.
            subst_ih.
        - subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply well_scons_alt.
              - eapply WellSubst_compr. all: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
              - econstructor. 2: eauto with sidecond.
                econstructor. 1: eauto with sidecond.
                subst_ih.
            }
            * econstructor. 2: eauto with sidecond.
              econstructor. 1: eauto with sidecond.
              subst_ih.
          + unfold ">>". cbn.
            eapply autosubst_simpl_WellSubst. 1: exact _.
            eapply well_scons_alt.
            * {
              eapply WellSubst_compr. all: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
            * {
              econstructor. 2: eauto with sidecond.
              econstructor.
              - econstructor. 1: eauto with sidecond.
                subst_ih.
              - subst_ih.
                eapply autosubst_simpl_WellSubst. 1: exact _.
                eapply well_scons_alt.
                + eapply well_scons_alt.
                  * eapply WellSubst_compr. all: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                  * econstructor. 2: eauto with sidecond.
                    econstructor. 1: eauto with sidecond.
                    subst_ih.
                + econstructor. 2: eauto with sidecond.
                  econstructor. 1: eauto with sidecond.
                  subst_ih.
            }
      }
      all:  reflexivity.
    + repeat subst_def. rasimpl. f_equal. f_equal. f_equal.
      all: rasimpl. all: reflexivity.
Qed.

Theorem subst_ty M Γ l t A Δ σ A' :
  ▹ M ⊢ Δ ->
  Δ ▹ M ⊢s σ : Γ ->
  Γ ▹ M ⊢< l > t : A ->
  A' = A <[ σ ] ->
  Δ ▹ M ⊢< l > t <[ σ ] : A'. 
Proof.
  intros. subst. eapply typing_conversion_subst in H1; eauto.
Qed.


Theorem subst_id M Γ :
  ▹ M ⊢ Γ ->
  Γ ▹ M ⊢s var : Γ.
Proof.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + eapply WellSubst_weak with (A := A) in ih; eauto.
      all:inversion H; eauto.
    + constructor; eauto. rasimpl. constructor.
Qed.

Lemma subst_one M Γ l A u :
  Γ ▹ M ⊢< l > u : A →
  Γ ▹ M ⊢s u .. : Γ ,, (l, A).
Proof.
  intros h.
  apply well_scons_alt.
  - apply subst_id; eauto using validity_ty_ctx.
  - rasimpl. assumption.
Qed.

Lemma WellSubst_conv M Γ Δ Ξ σ :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Δ ≡ Ξ →
  Γ ▹ M ⊢s σ : Ξ.
Proof.
  intros hs hc.
  induction hs as [| σ Δ l A hs ih h ] in Ξ, hc |- *.
  - inversion hc. constructor.
  - inversion hc. subst.
    constructor.
    + eapply ih. assumption.
    + eapply type_conv.
      * eassumption.
      * eapply meta_conv_conv.
        { eapply typing_conversion_subst. all: eauto using validity_ty_ctx. }
        reflexivity.
Qed.


(* We show weaker versions of conv_in_ctx in which we require the assumption ▹ M ⊢ Δ.
  Once we have validity, we then prove the real conv_in_ctx which drop this assumption. *)
Lemma pre_conv_in_ctx_ty M Γ Δ t l A :
  Γ ▹ M ⊢< l > t : A →
  ▹ M ⊢ Δ ->
  ▹ M ⊢ Δ ≡ Γ →
  Δ ▹ M ⊢< l > t : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma pre_conv_in_ctx_conv M Γ Δ u v l A :
  Γ ▹ M ⊢< l > u ≡ v : A →
  ▹ M ⊢ Δ ->
  ▹ M ⊢ Δ ≡ Γ →
  Δ ▹ M ⊢< l > u ≡ v : A.
Proof.
  intros h h' hc.
  eapply typing_conversion_subst with (σ := var) in h.
  - rasimpl in h. eassumption.
  - assumption.
  - eapply WellSubst_conv. 2: eassumption.
    apply subst_id. assumption.
Qed.

Lemma valid_varty M Γ x A l :
  ▹ M ⊢ Γ →
  Γ ∋< l > x : A →
  Γ ▹ M ⊢< Ax l > A : Sort l.
Proof.
  intros hΓ h.
  induction hΓ as [| Γ i B hΓ ih hB] in x, l, A, h |- *.
  1: inversion h.
  inversion h.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren. 3: eapply WellRen_S.
      1:eassumption. econstructor; eauto.
    + reflexivity.
  - subst.
    eapply meta_conv.
    + eapply typing_conversion_ren.
      2:econstructor; eauto.
    2: eapply WellRen_S.
      eapply ih. eassumption.
    + reflexivity.
Qed.

Lemma ctx_conv_refl M Γ :
  ▹ M ⊢ Γ →
  ▹ M ⊢ Γ ≡ Γ.
Proof.
  induction 1 as [| Γ l A h ih hA].
  - constructor.
  - constructor. 1: assumption.
    apply conv_refl. assumption.
Qed.

#[export] Instance ConvSubst_morphism M :
  Proper (eq ==> eq ==> (`=1`) ==> (`=1`) ==> iff) (ConvSubst M).
Proof.
  intros Γ ? <- Δ ? <- σ σ' e θ θ' e'.
  revert σ σ' e θ θ' e'. wlog_iff. intros σ σ' e θ θ' e' h.
  induction h as [| σ θ Δ l A h ih ho] in σ', e, θ', e' |- *.
  - constructor.
  - constructor.
    + eapply ih; unfold ">>". all: intro ; eauto.
    + rewrite <- e, <- e'. assumption.
Qed.

Lemma autosubst_simpl_ConvSubst M :
  ∀ Γ Δ s1 s2 s3 s4,
    SubstSimplification s1 s2 →
    SubstSimplification s3 s4 →
    Γ ▹ M ⊢s s1 ≡ s3 : Δ ↔ Γ ▹ M ⊢s s2 ≡ s4 : Δ.
Proof.
  intros ?????? h1 h2.
  apply ConvSubst_morphism. 1,2: eauto.
  - apply h1.
  - apply h2.
Qed.

#[export] Hint Rewrite -> autosubst_simpl_ConvSubst : rasimpl_outermost.

Lemma conv_scons_alt M Γ Δ σ θ u v l A :
  Γ ▹ M ⊢s σ ≡ θ : Δ →
  Γ ▹ M ⊢< l > u ≡ v : A <[ σ ] →
  Γ ▹ M ⊢s (u .: σ) ≡ (v .: θ) : Δ ,, (l, A).
Proof.
  intros hs hu.
  constructor.
  - erewrite autosubst_simpl_ConvSubst. 2,3: exact _.
    assumption.
  - cbn. rasimpl. assumption.
Qed.

Lemma ConvSubst_weak M Γ Δ σ θ l A :
  Γ ▹ M ⊢s σ ≡ θ : Δ →
  Γ ▹ M ⊢< Ax l > A : Sort l ->
  Γ ,, (l, A) ▹ M ⊢s (σ >> ren_term S) ≡ (θ >> ren_term S) : Δ.
Proof.
  induction 1 as [| σ θ Δ i B h ih ho] in l, A |- *.
  - constructor.
  - constructor.
    + auto.
    + eapply meta_conv_conv.
      * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
        1: econstructor; eauto using validity_ty_ctx.
        eapply WellRen_S.
      * rasimpl. reflexivity.
Qed.


Lemma ConvSubst_weak_two M Γ Δ σ θ l A l' B :
  Γ ▹ M ⊢s σ ≡ θ : Δ →
  ▹ M ⊢ Γ ,, (l, A) ,, (l', B ) ->
  Γ ,, (l, A) ,, (l', B) ▹ M ⊢s (σ >> ren_term (S >> S)) ≡ (θ >> ren_term (S >> S)) : Δ.
Proof.
  intros. induction H.
  1:econstructor.
  econstructor;eauto. 
  eapply meta_conv_conv.
  * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
   1:eauto.
   eapply WellRen_weak, WellRen_S.
  * rasimpl. reflexivity.
Qed.


Lemma ConvSubst_weak_three M Γ Δ σ θ l A l' B l'' C :
  Γ ▹ M ⊢s σ ≡ θ : Δ →
  ▹ M ⊢ Γ ,, (l, A) ,, (l', B ) ,, (l'', C) ->
  Γ ,, (l, A) ,, (l', B) ,, (l'', C) 
    ▹ M ⊢s (σ >> ren_term (S >> S >> S)) ≡ (θ >> ren_term (S >> S >> S)) : Δ.
Proof.
  intros. induction H.
  1:econstructor. 1:econstructor; eauto.
  eapply meta_conv_conv.
  * unfold ">>". eapply typing_conversion_ren. 1: eassumption.
   1:eauto.
   eapply WellRen_weak, WellRen_weak, WellRen_S.
  * rasimpl. reflexivity.
Qed.


Lemma conv_substs_up M Γ Δ σ σ' l A :
  Γ ▹ M ⊢s σ ≡ σ' : Δ →
  Γ ▹ M ⊢< Ax l > A <[ σ ] : Sort l ->
  Γ ,, (l, A <[ σ ]) ▹ M ⊢s up_term σ ≡ up_term σ' : Δ ,, (l, A).
Proof.
  intros h h'.
  apply conv_scons_alt.
  - apply ConvSubst_weak; assumption.
  - constructor. 
    1:eapply varty_meta.
    1:econstructor; eauto using validity_ty_ctx.
    1:rasimpl; reflexivity.
    constructor; eauto using validity_ty_ctx.
Qed.




Lemma conv_substs_up_two M Γ Δ σ σ' l l' B A A' B' :
  Γ ▹ M ⊢s σ ≡ σ' : Δ →
  ▹ M ⊢ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  A' = A <[ σ ] -> B' = B <[ up_term σ ] ->
  Γ ,, (l, A') ,, (l', B') ▹ M ⊢s up_term (up_term σ) ≡ up_term (up_term σ') : Δ ,, (l, A) ,, (l', B).
Proof.
  intros. subst. dependent destruction H0. dependent destruction H0.
  apply conv_scons_alt.
  - apply ConvSubst_weak. 1:eapply conv_substs_up; eauto. eauto.
  - constructor.
    1:eapply varty_meta.
    1:econstructor; eauto using validity_ty_ctx.
    1:rasimpl; reflexivity.
    constructor. 1:constructor; eauto using validity_ty_ctx. eauto.
Qed.

Theorem substs_id M Γ :
  ▹ M ⊢ Γ ->
  Γ ▹ M ⊢s var ≡ var : Γ.
Proof.
  intros.
  induction Γ as [| (l, A) Γ ih].
  - constructor.
  - constructor.
    + inversion H. eapply ConvSubst_weak with (A := A) in ih.
      all:eassumption.
    + constructor. 
      1:eapply varty_meta. 1:econstructor.
      1:rasimpl;reflexivity.
      assumption.
Qed.

Lemma substs_one M Γ l A u v :
  Γ ▹ M ⊢< l > u ≡ v : A →
  Γ ▹ M ⊢s u .. ≡ v .. : Γ ,, (l, A).
Proof.
  intros h.
  apply conv_scons_alt.
  - apply substs_id. eauto using validity_conv_ctx.
  - rasimpl. assumption.
Qed.

Lemma varty_conv_substs M Γ Δ σ θ x l A :
  Γ ∋< l > x : A →
  Δ ▹ M ⊢s σ ≡ θ : Γ →
  Δ ▹ M ⊢< l > σ x ≡ θ x : A <[ σ ].
Proof.
  intros hx hs.
  induction hs as [| σ θ Γ i B h ih ho] in x, l, A, hx |- *.
  1: inversion hx.
  inversion hx. all: subst.
  - rasimpl. assumption.
  - rasimpl. apply ih. assumption.
Qed.

Lemma subst_conv_meta_conv_ctx M Γ Δ σ τ Γ' :
  Γ ▹ M ⊢s σ ≡ τ : Δ ->
  Γ = Γ' ->
  Γ' ▹ M ⊢s σ ≡ τ : Δ.
Proof.
  intros. subst. assumption.
Qed.

Lemma subst_meta_conv_ctx M Γ Δ σ Γ' :
  Γ ▹ M ⊢s σ : Δ ->
  Γ = Γ' ->
  Γ' ▹ M ⊢s σ : Δ.
Proof.
  intros. subst. assumption.
Qed.


Lemma pre_conv_in_ctx_subst M Γ Γ' Δ σ :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Γ' ->
  ▹ M ⊢ Γ' ≡ Γ →
  Γ' ▹ M ⊢s σ : Δ.
Proof.
  intros. induction H. 1:econstructor.
  econstructor. 1:eauto.
  eapply pre_conv_in_ctx_ty; eauto.
Qed.

Lemma WellSubst_up_conv M Γ Δ l A A' σ :
  Γ ▹ M ⊢s σ : Δ →
  Γ ▹ M ⊢< Ax l > A' ≡ A <[ σ ] : Sort l ->
  Γ ▹ M ⊢< Ax l > A <[ σ ] : Sort l →
  Γ ▹ M ⊢< Ax l > A' : Sort l →
  Γ ,, (l, A') ▹ M ⊢s up_term σ : Δ ,, (l, A).
Proof.
  intros. subst.
  eapply pre_conv_in_ctx_subst.
  1:eapply WellSubst_up;eauto.
  all:econstructor;eauto using validity_ty_ctx, ctx_conv_refl.
Qed.


Lemma WellSubst_up_two_conv M Γ Δ σ l l' B A A' B' :
  Γ ▹ M ⊢s σ : Δ →
  ▹ M ⊢ Γ ,, (l, A') ,, (l', B') ->
  ▹ M ⊢ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  ▹ M ⊢ Γ ,, (l, A') ,, (l', B') ≡ Γ ,, (l, A <[ σ ]) ,, (l', B <[ up_term σ ]) ->
  Γ ,, (l, A') ,, (l', B') ▹ M ⊢s up_term (up_term σ) : Δ ,, (l, A) ,, (l', B).
Proof.
  intros.
  eapply pre_conv_in_ctx_subst.
  1:eapply WellSubst_up_two.
  all:eauto.
Qed.


Lemma conv_substs M Γ Δ σ σ' t l A :
  ▹ M ⊢ Δ ->
  Δ ▹ M ⊢s σ ≡ σ' : Γ →
  Δ ▹ M ⊢s σ : Γ →
  Δ ▹ M ⊢s σ' : Γ →
  Γ ▹ M ⊢< l > t : A →
  Δ ▹ M ⊢< l > t <[ σ ] ≡ t <[ σ' ] : A <[ σ ].
Proof.
  intros h hs hs' hst ht.
  induction ht in Δ, σ, σ', h, hs, hs', hst |- *; cbn.
  all : try solve [ econstructor ; eauto 15 using conv_substs_up, WellSubst_up_conv, WellSubst_up, ctx_typing, subst_ty ].
  - eauto using varty_conv_substs.
  - eapply meta_conv_conv.
    + econstructor. all: eauto 9 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    + rewrite closed_subst; eauto using typing_closed.
  - eapply meta_conv_conv.
    1:econstructor ; eauto 12 using WellSubst_up_conv, conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    rasimpl; reflexivity.
  - assert (Δ,, (ty 0, Nat) ▹ M ⊢< Ax l > P <[ up_term_term σ] : Sort l)
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    assert (Δ,, (ty 0, Nat) ▹ M ⊢< Ax l > P <[ up_term_term σ'] : Sort l) as h_
      by (eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up).
    assert (Δ,, (ty 0, Nat) ▹ M ⊢< Ax l > P <[ up_term_term σ] ≡ P <[ up_term_term σ'] : Sort l) as h__.
    1:{ eapply IHht1; eauto using ctx_typing, typing, WellSubst_up.
        change Nat with (Nat <[ σ ]) at 1.
        eapply conv_substs_up; eauto using typing. }
    eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 15 using ctx_typing, typing, WellSubst_up, WellSubst_up_conv, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] : Sort (ty n)) as Aσ_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ'] : Sort (ty n)) as Aσ'_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] ≡ A <[σ']: Sort (ty n)) as Aσ_conv_Aσ.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ])) as ΔAAσ.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ_Wt; eassumption. econstructor; eauto. } 
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ'.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ'_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ'_Wt;eassumption. econstructor; eauto. }      
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ]) ≡ 
      (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ_conv_ΔAAσ'.
    { econstructor. 1:econstructor; eauto using ctx_conv_refl. rasimpl. eapply IHht1; eauto using ctx_typing,WellSubst_weak, ConvSubst_weak. }
     rasimpl in ΔAAσ. 
     rasimpl in ΔAAσ'. rasimpl in ΔAAσ_conv_ΔAAσ'.
    eapply meta_conv_conv.
    1:econstructor; eauto.
    2:reflexivity.
    eapply IHht2; eauto.
    (* 1:rasimpl; eauto. *)
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    all:rasimpl; eauto.
    eapply WellSubst_up_two_conv; rasimpl; eauto.
  - assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] : Sort (ty n)) as Aσ_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ'] : Sort (ty n)) as Aσ'_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] ≡ A <[σ']: Sort (ty n)) as Aσ_conv_Aσ.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ])) as ΔAAσ.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ_Wt; eassumption. econstructor; eauto. } 
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ'.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ'_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ'_Wt;eassumption. econstructor; eauto. }      
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ]) ≡ 
      (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ_conv_ΔAAσ'.
    { econstructor. 1:econstructor; eauto using ctx_conv_refl. rasimpl. eapply IHht1; eauto using ctx_typing,WellSubst_weak, ConvSubst_weak. }
     rasimpl in ΔAAσ. 
     rasimpl in ΔAAσ'. rasimpl in ΔAAσ_conv_ΔAAσ'.
    econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    2:{ eapply meta_conv_conv. 1:eapply IHht4; eauto.
        unfold R', acc_wk, R_wk, A_wk; rasimpl; reflexivity. }
    1:{ eapply IHht2.
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    all:rasimpl; eauto.
    eapply WellSubst_up_two_conv; rasimpl; eauto. }
  - assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] : Sort (ty n)) as Aσ_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ'] : Sort (ty n)) as Aσ'_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] ≡ A <[σ']: Sort (ty n)) as Aσ_conv_Aσ.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ])) as ΔAAσ.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ_Wt; eassumption. econstructor; eauto. } 
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ'.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ'_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ'_Wt;eassumption. econstructor; eauto. }      
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ]) ≡ 
      (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ_conv_ΔAAσ'.
    { econstructor. 1:econstructor; eauto using ctx_conv_refl. rasimpl. eapply IHht1; eauto using ctx_typing,WellSubst_weak, ConvSubst_weak. }
     rasimpl in ΔAAσ. 
     rasimpl in ΔAAσ'. rasimpl in ΔAAσ_conv_ΔAAσ'.
    econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    1:{ eapply IHht2.
    2:eapply conv_substs_up_two; eauto.
    4:eapply WellSubst_up_two; eauto.
    all:rasimpl; eauto.
    eapply WellSubst_up_two_conv; rasimpl; eauto. }
    1:eapply meta_conv_conv.
    1:eapply IHht6;eauto.
    all:rasimpl; eauto.
    - assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] : Sort (ty n)) as Aσ_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ'] : Sort (ty n)) as Aσ'_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] ≡ A <[σ']: Sort (ty n)) as Aσ_conv_Aσ.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ])) as ΔAAσ.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ_Wt; eassumption. econstructor; eauto. } 
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ'.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ'_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ'_Wt;eassumption. econstructor; eauto. }      
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ]) ≡ 
      (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ_conv_ΔAAσ'.
    { econstructor. 1:econstructor; eauto using ctx_conv_refl. rasimpl. eapply IHht1; eauto using ctx_typing,WellSubst_weak, ConvSubst_weak. }
        rasimpl in ΔAAσ. 
     rasimpl in ΔAAσ'. rasimpl in ΔAAσ_conv_ΔAAσ'.
     

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ01.
  {   econstructor. 1:econstructor.
      1:eapply WellSubst_weak_two; eauto.
      1:ssimpl. 1:eapply meta_conv. 1:econstructor.
      2:econstructor. 1:eauto. 1:rasimpl; reflexivity.
      1:eapply meta_conv. 1:econstructor.
      1:eauto. 1:econstructor. 1:econstructor. 1:rasimpl; reflexivity. } 

  assert ((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ' >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ'01.
  {   econstructor. 1:econstructor.
      1:eapply WellSubst_weak_two; eauto.
      1:ssimpl. 1:eapply meta_conv. 1:econstructor.
      2:econstructor. 1:eauto. 1:rasimpl; reflexivity.
      1:eapply meta_conv. 1:econstructor.
      1:eauto. 1:econstructor. 1:econstructor. 1:rasimpl; reflexivity. } 

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ >> ren_term (S >> S))) 
      ≡ ((var 1) .: ((var 0) .: σ' >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ01_conv_σ'01.
  {   econstructor. 1:econstructor.
      2,3:ssimpl. 2,3:econstructor; eauto.
      2,3:eapply varty_meta.
      2:econstructor. 3:econstructor;econstructor.
      2,3:rasimpl;eauto.
      eapply ConvSubst_weak_two; eauto. }

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ >> ren_term (S >> S))] : Sort prop) as Rσ.
    { eapply typing_conversion_subst in ht2; simpl in ht2; rasimpl; eauto. }

  assert ((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ' >> ren_term (S >> S))] : Sort prop) as Rσ'.
    { eapply typing_conversion_subst in ht2; simpl in ht2; rasimpl; eauto. }
    
  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ >> ren_term (S >> S))] 
    ≡ R <[ var 1 .: (var 0 .: σ' >> ren_term (S >> S))] : Sort prop) as Rσ_conv_Rσ'.
    { eapply IHht2; eauto.
      eapply pre_conv_in_ctx_subst. 1:eauto.
      all:eauto. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ1.
   { econstructor.
    1:ssimpl; eapply WellSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }

  assert (((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ' >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ' >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ'1.
   { econstructor.
    1:ssimpl; eapply WellSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ >> ren_term (S >> (S >> S)))
      ≡ ((var 1) .: σ' >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ1_conv_σ1'.
   { econstructor.
    1:ssimpl; eapply ConvSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }



  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax l > P <[ (var 1) .: σ >> ren_term (S >> (S >> S))] : Sort l) as Pσ.
  { eapply subst_ty; eauto using ctx_typing. }


  assert (((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ' >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax l > P <[ (var 1) .: σ' >> ren_term (S >> (S >> S))] : Sort l) as Pσ'.
  { eapply subst_ty; eauto using ctx_typing. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax l > P <[ (var 1) .: σ >> ren_term (S >> (S >> S))]
          ≡ P <[ (var 1) .: σ' >> ren_term (S >> (S >> S))] : Sort l) 
        as Pσ_conv_Pσ'.
  { eapply meta_conv_conv. 1:eapply IHht3; eauto.
    2:eapply pre_conv_in_ctx_subst.
    2:eauto.
    all:eauto.
    3:econstructor; eauto.
    1,2:econstructor; eauto. }

  assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (Ru (ty n) l, B <[ up_term_term σ])) as ΔABσ.
  {  econstructor; eauto using ctx_typing.
     unfold B, R', P'. rasimpl.
     econstructor. 1:dependent destruction ΔAAσ; eauto.
      eapply meta_lvl.
      1:eapply meta_conv.
      1:econstructor.
      3,4:destruct l;reflexivity.
      all:eauto. }

  assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (Ru (ty n) l, B <[ up_term_term σ'])) as ΔABσ'.
  {  econstructor; eauto using ctx_typing.
     unfold B, R', P'. rasimpl.
     econstructor. 1:dependent destruction ΔAAσ'; eauto.
      eapply meta_lvl.
      1:eapply meta_conv.
      1:econstructor.
      3,4:destruct l;reflexivity.
      all:eauto. }


    eapply meta_conv_conv.
    1:{  econstructor; eauto 7 using subst_ty, ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx, WellSubst_up_conv.
      * eapply subst_ty; rasimpl; eauto using WellSubst_up. eapply WellSubst_up_two; rasimpl; eauto.
      * eapply IHht2; eauto. 1:rasimpl;eauto.
        ** eapply conv_substs_up_two; rasimpl; eauto.
        ** eapply WellSubst_up_two; rasimpl; eauto.
        ** eapply WellSubst_up_two_conv; rasimpl; eauto.
      * eapply meta_conv_conv. 
        ** eapply IHht4; eauto.
          *** unfold B, R', P' in ΔABσ. rasimpl in ΔABσ. rasimpl. eauto. 
          *** eapply conv_substs_up_two; eauto.
              unfold B, R',P';rasimpl; eauto.
          *** eapply WellSubst_up_two; eauto.
              unfold B, R',P';rasimpl; eauto.
          *** eapply WellSubst_up_two_conv; eauto.
              1:unfold B, R', P' in ΔABσ; rasimpl in ΔABσ; rasimpl; eauto. 
              econstructor. 1:dependent destruction ΔAAσ_conv_ΔAAσ'; eauto.
              econstructor; fold subst_term.
              1,2:rasimpl; inversion ΔAAσ; inversion ΔAAσ_conv_ΔAAσ'; eauto.
              unfold R',P'.
              eapply meta_lvl_conv.
              1:eapply meta_conv_conv.
              1:econstructor.
              4,5:destruct l;reflexivity.
              all:ssimpl.
              1:eapply subst_ty; eauto.
              1:eapply meta_conv_conv. 
              1:eapply IHht2; eauto.
              2:rasimpl;reflexivity.
              1:eapply pre_conv_in_ctx_subst;eauto.
              1:eapply meta_conv_conv. 
              1:eapply IHht3; eauto using ctx_typing.
              1:eapply pre_conv_in_ctx_subst. 1:eauto.
              all:eauto using ctx_typing.
              econstructor;eauto.
        ** unfold P''; rasimpl; reflexivity. }
    rasimpl. reflexivity.
- assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] : Sort (ty n)) as Aσ_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ'] : Sort (ty n)) as Aσ'_Wt.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (Δ ▹ M ⊢< Ax (ty n) > A <[σ] ≡ A <[σ']: Sort (ty n)) as Aσ_conv_Aσ.
    { eapply typing_conversion_subst in ht1; eauto using typing, ctx_typing, WellSubst_up. }
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ])) as ΔAAσ.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ_Wt; eassumption. econstructor; eauto. } 
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ'.
    { econstructor. 1:econstructor; eauto. rasimpl. eapply typing_conversion_ren in Aσ'_Wt. 
      3:eapply WellRen_S. 1:rasimpl in Aσ'_Wt;eassumption. econstructor; eauto. }      
    assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (ty n, (S ⋅ A) <[ up_term σ]) ≡ 
      (Δ,, (ty n, A <[ σ'])),, (ty n, (S ⋅ A) <[ up_term σ'])) as ΔAAσ_conv_ΔAAσ'.
    { econstructor. 1:econstructor; eauto using ctx_conv_refl. rasimpl. eapply IHht1; eauto using ctx_typing,WellSubst_weak, ConvSubst_weak. }
        rasimpl in ΔAAσ. 
     rasimpl in ΔAAσ'. rasimpl in ΔAAσ_conv_ΔAAσ'.
     

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ01.
  {   econstructor. 1:econstructor.
      1:eapply WellSubst_weak_two; eauto.
      1:ssimpl. 1:eapply meta_conv. 1:econstructor.
      2:econstructor. 1:eauto. 1:rasimpl; reflexivity.
      1:eapply meta_conv. 1:econstructor.
      1:eauto. 1:econstructor. 1:econstructor. 1:rasimpl; reflexivity. } 

  assert ((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ' >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ'01.
  {   econstructor. 1:econstructor.
      1:eapply WellSubst_weak_two; eauto.
      1:ssimpl. 1:eapply meta_conv. 1:econstructor.
      2:econstructor. 1:eauto. 1:rasimpl; reflexivity.
      1:eapply meta_conv. 1:econstructor.
      1:eauto. 1:econstructor. 1:econstructor. 1:rasimpl; reflexivity. } 

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])
    ▹ M ⊢s ((var 1) .: ((var 0) .: σ >> ren_term (S >> S))) 
      ≡ ((var 1) .: ((var 0) .: σ' >> ren_term (S >> S))) 
      : (Γ,, (ty n, A)),, (ty n, S ⋅ A)) as σ01_conv_σ'01.
  {   econstructor. 1:econstructor.
      2,3:ssimpl. 2,3:econstructor; eauto.
      2,3:eapply varty_meta.
      2:econstructor. 3:econstructor;econstructor.
      2,3:rasimpl;eauto.
      eapply ConvSubst_weak_two; eauto. }

  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ >> ren_term (S >> S))] : Sort prop) as Rσ.
    { eapply typing_conversion_subst in ht2; simpl in ht2; rasimpl; eauto. }

  assert ((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ' >> ren_term (S >> S))] : Sort prop) as Rσ'.
    { eapply typing_conversion_subst in ht2; simpl in ht2; rasimpl; eauto. }
    
  assert ((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S]) ▹ M ⊢< Ax prop > 
    R <[ var 1 .: (var 0 .: σ >> ren_term (S >> S))] 
    ≡ R <[ var 1 .: (var 0 .: σ' >> ren_term (S >> S))] : Sort prop) as Rσ_conv_Rσ'.
    { eapply IHht2; eauto.
      eapply pre_conv_in_ctx_subst. 1:eauto.
      all:eauto. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ1.
   { econstructor.
    1:ssimpl; eapply WellSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }

  assert (((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ' >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ' >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ'1.
   { econstructor.
    1:ssimpl; eapply WellSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
    (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))])
    ▹ M ⊢s ((var 1) .: σ >> ren_term (S >> (S >> S)))
      ≡ ((var 1) .: σ' >> ren_term (S >> (S >> S))) : Γ,, (ty n, A)) as σ1_conv_σ1'.
   { econstructor.
    1:ssimpl; eapply ConvSubst_weak_three; eauto using ctx_typing.
    ssimpl.
    econstructor; eauto using ctx_typing.
    eapply varty_meta.
    1:econstructor;econstructor. rasimpl. reflexivity. }



  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax (ty m) > P <[ (var 1) .: σ >> ren_term (S >> (S >> S))] : Sort (ty m)) as Pσ.
  { eapply subst_ty; eauto using ctx_typing. }


  assert (((Δ,, (ty n, A <[ σ'])),, (ty n, A <[ σ' >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ' >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax (ty m) > P <[ (var 1) .: σ' >> ren_term (S >> (S >> S))] : Sort (ty m)) as Pσ'.
  { eapply subst_ty; eauto using ctx_typing. }

  assert (((Δ,, (ty n, A <[ σ])),, (ty n, A <[ σ >> ren_term S])),,
        (prop, R <[ (var 1) .: ((var 0) .: σ >> ren_term (S >> S))]) 
        ▹ M ⊢< Ax (ty m) > P <[ (var 1) .: σ >> ren_term (S >> (S >> S))]
          ≡ P <[ (var 1) .: σ' >> ren_term (S >> (S >> S))] : Sort (ty m)) 
        as Pσ_conv_Pσ'.
  { eapply meta_conv_conv. 1:eapply IHht3; eauto.
    2:eapply pre_conv_in_ctx_subst.
    2:eauto.
    all:eauto.
    3:econstructor; eauto.
    1,2:econstructor; eauto. }

  assert (▹ M ⊢ (Δ,, (ty n, A <[ σ])),, (Ru (ty n) (ty m), B <[ up_term_term σ])) as ΔABσ.
  {  econstructor; eauto using ctx_typing.
     unfold B, R', P'. rasimpl.
     econstructor. 1:dependent destruction ΔAAσ; eauto.
      eapply meta_lvl.
      1:eapply meta_conv.
      1:econstructor.
      3,4:reflexivity.
      all:eauto. }

  assert (▹ M ⊢ (Δ,, (ty n, A <[ σ'])),, (Ru (ty n) (ty m), B <[ up_term_term σ'])) as ΔABσ'.
  {  econstructor; eauto using ctx_typing.
     unfold B, R', P'. rasimpl.
     econstructor. 1:dependent destruction ΔAAσ'; eauto.
      eapply meta_lvl.
      1:eapply meta_conv.
      1:econstructor.
      3,4:reflexivity.
      all:eauto. }
    eapply meta_conv_conv.
    1:econstructor; eauto 10 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty.
    2:eapply IHht2.
    3:eapply conv_substs_up_two; eauto.
    5:eapply WellSubst_up_two; eauto.
    1:eapply typing_conversion_subst in ht2; eauto.
    2:eapply WellSubst_up_two; eauto.
    1-8,10:rasimpl; eauto.
    4:{ rasimpl. f_equal. f_equal. unfold t5, t4, t3, t2, t1, t0, Awk, Rwk, Pwk, pwk,P'', B, P', R'.
      simpl. f_equal. f_equal. 1:ssimpl ; substify; reflexivity.
      f_equal; rasimpl. 1-2:reflexivity.
      f_equal. }
      * eauto 7 using subst_ty, ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx, WellSubst_up_conv. 
      * eapply WellSubst_up_two_conv; rasimpl; eauto.
      * eapply meta_conv_conv. 
        ** eapply IHht4; eauto.
          *** unfold B, R', P' in ΔABσ. rasimpl in ΔABσ. rasimpl. eauto. 
          *** eapply conv_substs_up_two; eauto.
              unfold B, R',P';rasimpl; eauto.
          *** eapply WellSubst_up_two; eauto.
              unfold B, R',P';rasimpl; eauto.
          *** eapply WellSubst_up_two_conv; eauto.
              1:unfold B, R', P' in ΔABσ; rasimpl in ΔABσ; rasimpl; eauto. 
              econstructor. 1:dependent destruction ΔAAσ_conv_ΔAAσ'; eauto.
              econstructor; fold subst_term.
              1,2:rasimpl; inversion ΔAAσ; inversion ΔAAσ_conv_ΔAAσ'; eauto.
              unfold R',P'.
              eapply meta_lvl_conv.
              1:eapply meta_conv_conv.
              1:econstructor.
              4,5:reflexivity.
              all:ssimpl.
              1:eapply subst_ty; eauto.
              1:eapply meta_conv_conv. 
              1:eapply IHht2; eauto.
              2:rasimpl;reflexivity.
              1:eapply pre_conv_in_ctx_subst;eauto.
              1:eapply meta_conv_conv. 
              1:eapply IHht3; eauto using ctx_typing.
              1:eapply pre_conv_in_ctx_subst. 1:eauto.
              all:eauto using ctx_typing.
              econstructor;eauto.
        ** unfold P''; rasimpl; reflexivity.
    
  - eapply meta_conv_conv.
    + econstructor.
          all : try solve [ (eapply meta_conv_conv + eapply meta_conv) ; [
        eauto 12 using subst_ty, ctx_typing, typing, WellSubst_up, conv_substs_up, subst_conv_meta_conv_ctx, subst_meta_conv_ctx, WellSubst_up_conv | rasimpl ; reflexivity]].
    + rasimpl; reflexivity.
  - eapply meta_conv_conv.
    1:try solve [ econstructor ; eauto 12 using conv_substs_up, WellSubst_up, ctx_typing, subst_ty, WellSubst_up_conv ].
    rasimpl; reflexivity.
  - eapply conv_conv. 1: eauto.
    eapply meta_conv_conv.
    + eapply typing_conversion_subst; eauto. all: eauto.
    + reflexivity.
Qed.

Theorem pre_subst_conv M Γ l t u A Δ σ τ A' :
  ▹ M ⊢ Δ →
  Δ ▹ M ⊢s σ : Γ ->
  Δ ▹ M ⊢s σ ≡ τ : Γ ->
  Δ ▹ M ⊢s τ : Γ ->
  Γ ▹ M ⊢< l > t : A ->
  Γ ▹ M ⊢< l > u : A ->
  Γ ▹ M ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ▹ M ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros hΔ hσ hστ hτ ht hu htu ->.
  eapply conv_trans.
  - eapply typing_conversion_subst in htu. all: eauto.
  - eapply conv_substs; eauto.
Qed.


Lemma subst_id_reduce1 : pointwise_relation _ eq (var 0 .: (S >> var)) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a; reflexivity.
Qed.

Lemma subst_id_reduce2 : pointwise_relation _ eq (var 0 .: (var 1 .: (S >> (S >> var)))) var.
Proof.
    unfold pointwise_relation. intros.
    destruct a. 1:reflexivity. destruct a. 1:reflexivity. reflexivity.
Qed.

Section AccCompValidity.

  Context M (Γ : ctx) (n : nat) (A R : term)
    (AWt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (RWt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop).
  Let R0 := (1 .: (0 .: (S >> S))) ⋅ R.

  Lemma R0Wt : Γ,, (ty n, A),, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R0 : Sort prop.
  Proof.
    unfold R0.
    eapply type_ren; eauto using validity_ty_ctx.
    econstructor. 1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. rasimpl; reflexivity.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl;reflexivity.
  Qed.

  Context (l : level) (P : term) (PWt : Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l).
  Let P0 := (1 .: (S >> S >> S)) ⋅ P.
  Let B := Pi (ty n) l (S ⋅ A) (Pi prop l R0 P0).
  Let P00 := (1.: (S >> S)) ⋅ P.

  Lemma P0Wt : Γ,, (ty n, A),, (ty n, S ⋅ A),, (prop, R0) ▹ M ⊢< Ax l > P0 : Sort l.
  Proof.
    unfold P0.
    eapply type_ren;eauto.
    1:econstructor; eauto using validity_ty_ctx, R0Wt.
    1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Lemma BWt : Γ,, (ty n, A)▹ M ⊢< Ax (Ru (ty n) l) > B : Sort (Ru (ty n) l).
  Proof.
    unfold B.
    econstructor.
    1:eapply type_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    1:eapply meta_lvl. 1:eapply meta_conv.
    1:econstructor; eauto using R0Wt, P0Wt.
    all: destruct l; reflexivity.
  Qed.

  Lemma P00Wt : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< Ax l > P00 : Sort l.
  Proof.
    unfold P00.
    eapply type_ren; eauto.
    1:econstructor; eauto using validity_ty_ctx, BWt.
    econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl. reflexivity.
  Qed.

  Context (a : term)
    (aWt : Γ ▹ M ⊢< ty n > a : A).
    Let t2 := R<[S ⋅ a .: (var 0 .: S >> var)].

  Lemma t2Wt : Γ ,, (ty n, A) ▹ M ⊢< Ax prop > t2 : Sort prop.
  Proof.
    unfold t2.
    eapply subst_ty; eauto using validity_ty_ctx.
    econstructor.
    1:econstructor.
    - ssimpl. change (S >> var) with (var >> ren_term S). eapply WellSubst_weak; eauto using subst_id, validity_ty_ctx.
    - ssimpl. eapply meta_conv. 1:econstructor. 2:econstructor. 1:eauto using validity_ty_ctx. rasimpl. reflexivity.
    - ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx. 1:eapply WellRen_S. rasimpl. reflexivity.
  Qed.

  Context (p q : term)
    (pWt : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p : P00)
    (qWt : Γ ▹ M ⊢< prop > q : acc (ty n) A R a).
  Let Awk := (S >> S) ⋅ A.
  Let Rwk := (up_ren (up_ren (S >> S))) ⋅ R.
  Let Pwk := (up_ren (S >> S)) ⋅ P.
  Let pwk := (up_ren (up_ren (S >> S))) ⋅ p.
  Let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0).
  Let t1 := accel (ty n) l Awk Rwk Pwk pwk (var 1) t0.
  Let t3 := lam prop l t2 P00 t1.
  Let t4 := Pi prop l t2 P00.
  Let t5 := lam (ty n) l A t4 t3.




  Lemma AwkWt : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< Ax (ty n) > Awk : Sort (ty n).
  Proof.
    unfold Awk.
    eapply type_ren; eauto using validity_ty_ctx.
    1:econstructor; eauto using validity_ty_ctx, t2Wt.
    eapply WellRen_weak, WellRen_S.
  Qed.

  Lemma RwkWt : Γ ,, (ty n, A) ,, (prop, t2),, (ty n, Awk) ,, (ty n, S ⋅ Awk) ▹ M ⊢< Ax prop > Rwk : Sort prop.
  Proof.
    unfold Rwk, Awk.
    eapply type_ren; eauto.
    1:econstructor. 1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    1:ssimpl. 1:eapply type_ren; eauto. 1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    1:eapply WellRen_weak, WellRen_weak, WellRen_S.
    eapply WellRen_up. 1:eapply WellRen_up. 1:eapply WellRen_weak, WellRen_S. all:rasimpl; reflexivity.
  Qed.

  Lemma PwkWt : Γ ,, (ty n, A) ,, (prop, t2),, (ty n, Awk) ▹ M ⊢< Ax l > Pwk : Sort l.
  Proof.
    unfold Pwk, Awk.
    eapply type_ren; eauto.
    1:econstructor. 2:fold Awk. 1,2:eauto using validity_ty_ctx, AwkWt.
    eapply WellRen_up. 1:eapply WellRen_weak, WellRen_S. reflexivity.
  Qed.

  Lemma pwkWt : Γ ,, (ty n, A) ,, (prop, t2) ,, (ty n, Awk) ,, (Ru (ty n) l, (up_ren (S >> S)) ⋅ B) ▹ M ⊢< l > pwk : (up_ren (up_ren (S >> S))) ⋅ P00.
  Proof.
    unfold pwk, Awk. eapply type_ren; eauto.
    1:econstructor; eauto using PwkWt, validity_ty_ctx.
    1:eapply type_ren; eauto using BWt, validity_ty_ctx, PwkWt.
    1:eapply WellRen_up.
    1:eapply WellRen_weak, WellRen_S.
    1:reflexivity.
    1:eapply WellRen_up. 1:eapply WellRen_up.
    1:eapply WellRen_weak, WellRen_S.
    all: ssimpl; reflexivity.
  Qed.

  Lemma t0Wt : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< prop > t0 : acc (ty n) Awk Rwk (var 1).
  Proof.
    unfold t0.
    econstructor; eauto using AwkWt, RwkWt, PwkWt.
    - eapply type_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - eapply type_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. 1:unfold Awk; rasimpl; reflexivity.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:unfold Rwk, t2; rasimpl; simpl; reflexivity.
  Qed.

  Lemma t1Wt : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< l > t1 : Pwk <[ (var 1) .. ].
  Proof.
    unfold t1.
    econstructor; eauto using AwkWt, RwkWt, PwkWt, t0Wt.
    - eassert (Pi _ l (S ⋅ Awk) (Pi prop l ((1 .: (0 .: S >> S)) ⋅ Rwk) ((1 .: (S >> S) >> S) ⋅ Pwk)) = (up_ren (S >> S)) ⋅ B).
      1: {unfold B, Awk, Rwk, Pwk, R0, P0. rasimpl. reflexivity. }
      rewrite H; eapply meta_conv.
      1: eapply pwkWt. unfold P00, Pwk; rasimpl; reflexivity.
    - econstructor; eauto using t0Wt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. unfold Awk; rasimpl; reflexivity.
  Qed.

  Lemma P00Wt2 : (Γ,, (ty n, A)),, (prop, t2) ▹ M ⊢< Ax l > P00 : Sort l.
  Proof.
    unfold P00. eapply type_ren; eauto using t1Wt, validity_ty_ctx.
    econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Lemma t3Wt : Γ ,, (ty n, A) ▹ M ⊢< l > t3 : Pi prop l t2 P00.
  Proof.
    unfold t3. eapply meta_lvl.
    1:econstructor; eauto using t2Wt, P00Wt2.
    1:eapply meta_conv. 1:eapply t1Wt.
    1:unfold Pwk, P00; substify; ssimpl; reflexivity.
    destruct l; eauto.
  Qed.

  Lemma t4Wt : Γ ,, (ty n, A) ▹ M ⊢< Ax l > t4 : Sort l.
  Proof.
    unfold t4. eapply meta_conv. 1:eapply meta_lvl.
    1:econstructor; eauto using t2Wt, P00Wt2.
    all:destruct l; reflexivity.
  Qed.

  Lemma t5Wt : Γ ▹ M ⊢< Ru (ty n) l > t5 : Pi (ty n) l A t4.
  Proof.
    unfold t5. econstructor; eauto using t3Wt, t4Wt.
  Qed.

End AccCompValidity.
Section AccCompValidityConv.

  Context M (Γ : ctx) (n : nat) (l : level) (A : term)
    (AWt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n)).

  Context (A' : term)
    (AWt' : Γ ▹ M ⊢< Ax (ty n) > A' : Sort (ty n)).

  Context 
    (A_conv_A' : Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n)).


  Lemma Γ_A_SA' : ▹ M ⊢ Γ ,, (ty n, A') ,, (ty n, S ⋅ A').
  Proof.
    econstructor. 1:econstructor; eauto using validity_ty_ctx.
    eapply type_ren; eauto. 1:econstructor; eauto using validity_ty_ctx.
    eapply WellRen_S.
  Qed.

  Lemma Γ_A_SA_conv : ▹ M ⊢ Γ ,, (ty n, A') ,, (ty n, S ⋅ A') ≡ Γ ,, (ty n, A) ,, (ty n, S ⋅ A).
  Proof.
    econstructor. 1:econstructor; eauto using ctx_conv_refl, validity_ty_ctx, conv_sym.
    eapply conv_ren; eauto using validity_ty_ctx, conv_sym. 2: eapply WellRen_S.
    econstructor; eauto using validity_ty_ctx.
  Qed.



  Context (R R' : term)
    (RWt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (RWt' : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R' : Sort prop)
    (R_conv_R' : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop).
    Let R0 := (1 .: (0 .: (S >> S))) ⋅ R.
    Let R0' := (1 .: (0 .: (S >> S))) ⋅ R'.

    Lemma R0_conv_R0' : Γ,, (ty n, A),, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R0 ≡ R0' : Sort prop.
  Proof.
    unfold R0.
    eapply conv_ren; eauto using validity_ty_ctx.
    econstructor. 1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. rasimpl; reflexivity.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl;reflexivity.
  Qed.

  Context (P P' : term)
    (PWt : Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l)
    (PWt' : Γ ,, (ty n, A) ▹ M ⊢< Ax l > P' : Sort l)
    (P_conv_P' : Γ ,, (ty n, A) ▹ M ⊢< Ax l > P ≡ P' : Sort l).
    Let P0 := (1 .: (S >> S >> S)) ⋅ P.
    Let P0' := (1 .: (S >> S >> S)) ⋅ P'.
  Lemma P0_conv_P0' : Γ,, (ty n, A),, (ty n, S ⋅ A),, (prop, R0) ▹ M ⊢< Ax l > P0 ≡ P0' : Sort l.
  Proof.
    unfold P0.
    eapply conv_ren;eauto.
    1:econstructor; eauto using validity_ty_ctx, R0Wt.
    1:econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Let B := Pi (ty n) l (S ⋅ A) (Pi prop l R0 P0).
  Let P00 := (1.: (S >> S)) ⋅ P.
  Let B' := Pi (ty n) l (S ⋅ A') (Pi prop l R0' P0').
  Let P00' := (1.: (S >> S)) ⋅ P'.
  Context (p : term)
    (pWt : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p : P00).


  Lemma B_conv_B' : Γ,, (ty n, A)▹ M ⊢< Ax (Ru (ty n) l) > B ≡ B' : Sort (Ru (ty n) l).
  Proof.
    unfold B.
    econstructor.
    1:eapply type_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    1:eapply conv_ren; eauto using validity_ty_ctx.
    1:eapply WellRen_S.
    eapply meta_lvl_conv. 1:eapply meta_conv_conv.
    1:econstructor; eauto using R0_conv_R0', P0_conv_P0', R0Wt.
    all: destruct l; reflexivity.
  Qed.

  Lemma P00_conv_P00' : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< Ax l > P00 ≡ P00' : Sort l.
  Proof.
    unfold P00.
    eapply conv_ren; eauto using validity_ty_ctx.
    econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl. reflexivity.
  Qed.

  (* Lemma Γ_A_B' : ▹ M ⊢ Γ ,, (i, A') ,, (Ru i l, B').
  Proof.
    econstructor. 1:econstructor; eauto using validity_ty_ctx.

    eapply BWt. *)

  Lemma Γ_A_B_conv : ▹ M ⊢ Γ ,, (ty n, A') ,, (Ru (ty n) l, B') ≡ Γ ,, (ty n, A) ,, (Ru (ty n) l, B).
  Proof.
    econstructor. 1:econstructor.
    all:eauto using A_conv_A', B_conv_B', ctx_conv_refl, validity_ty_ctx, conv_sym, pre_conv_in_ctx_conv.
    eapply pre_conv_in_ctx_conv; eauto using conv_sym, B_conv_B'.
    1:econstructor; eauto using validity_ty_ctx.
    econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
  Qed.

  Context (a a' : term)
    (aWt : Γ ▹ M ⊢< ty n > a : A)
    (aWt' : Γ ▹ M ⊢< ty n > a' : A)
    (a_conv_a' : Γ ▹ M ⊢< ty n > a ≡ a' : A).
  Let t2' := R' <[S ⋅ a' .: (var 0 .: S >> var)].
  Let t2 := R<[S ⋅ a .: (var 0 .: S >> var)].
  Let Awk := (S >> S) ⋅ A.
  Let Awk' := (S >> S) ⋅ A'.

  Lemma t2_conv_t2' : Γ ,, (ty n, A) ▹ M ⊢< Ax prop > t2 ≡ t2' : Sort prop.
  Proof.
    unfold t2, t2'.

    eapply pre_subst_conv; eauto using validity_ty_ctx.
    - econstructor. 1:{ssimpl. rewrite subst_id_reduce1. eapply subst_id. eauto using validity_ty_ctx. }
      ssimpl. eapply type_ren; eauto using WellRen_S, validity_ty_ctx. rasimpl. reflexivity.
    - econstructor.  1:{ssimpl. rewrite subst_id_reduce1. eapply refl_subst, subst_id. eauto using validity_ty_ctx. }
      ssimpl. eapply conv_ren; eauto using WellRen_S, validity_ty_ctx. rasimpl. reflexivity.
    - econstructor. 1:{ssimpl. rewrite subst_id_reduce1. eapply subst_id. eauto using validity_ty_ctx. }
      ssimpl. eapply type_ren; eauto using WellRen_S, validity_ty_ctx. rasimpl. reflexivity.
  Qed.


  Lemma Awk_conv_Awk' : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< Ax (ty n) > Awk ≡ Awk' : Sort (ty n).
  Proof.
    unfold Awk, Awk'.
    eapply conv_ren; eauto using validity_ty_ctx, ctx_typing, t2Wt, WellRen_weak, WellRen_S. 
  Qed.


  Lemma P00_conv_P00'2 : (Γ,, (ty n, A)),, (prop, t2) ▹ M ⊢< Ax l > P00 ≡ P00' : Sort l.
  Proof.
    unfold P00, P00'. eapply conv_ren; eauto using t1Wt, validity_ty_ctx, AwkWt.
    econstructor.
    - ssimpl. eapply WellRen_weak, WellRen_S.
    - ssimpl. eapply varty_meta. 1:econstructor. 1:econstructor. rasimpl; reflexivity.
  Qed.

  Context (q : term) (p' q' : term)
    (pWt' : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p' : P00)
    (p_conv_p' : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p ≡ p' : P00).
  Context 
    (qWt : Γ ▹ M ⊢< prop > q : acc (ty n) A R a)
    (qWt' : Γ ▹ M ⊢< prop > q' : acc (ty n) A R a)
    (q_conv_q' : Γ ▹ M ⊢< prop > q ≡ q' : acc (ty n) A R a).
  Let Rwk := (up_ren (up_ren (S >> S))) ⋅ R.
  Let Pwk := (up_ren (S >> S)) ⋅ P.
  Let pwk := (up_ren (up_ren (S >> S))) ⋅ p.
  Let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0).
  Let t1 := accel (ty n) l Awk Rwk Pwk pwk (var 1) t0.
  Let t3 := lam prop l t2 P00 t1.
  Let t4 := Pi prop l t2 P00.
  Let t5 := lam (ty n) l A t4 t3.

  Let Rwk' := (up_ren (up_ren (S >> S))) ⋅ R'.
  Let Pwk' := (up_ren (S >> S)) ⋅ P'.
  Let pwk' := (up_ren (up_ren (S >> S))) ⋅ p'.
  Let t0' := accinv (ty n) Awk' Rwk' ((S >> S) ⋅ a') ((S >> S) ⋅ q') (var 1) (var 0).
  Let t1' := accel (ty n) l Awk' Rwk' Pwk' pwk' (var 1) t0'.
  Let t3' := lam prop l t2' P00' t1'.
  Let t4' := Pi prop l t2' P00'.
  Let t5' := lam (ty n) l A' t4' t3'.



  Lemma Rwk_conv_Rwk' : Γ ,, (ty n, A) ,, (prop, t2),, (ty n, Awk) ,, (ty n, S ⋅ Awk) ▹ M ⊢< Ax prop > Rwk ≡ Rwk' : Sort prop.
  Proof.
    unfold Rwk, Awk, Rwk'.
    eapply conv_ren; eauto.
    2:{ eapply WellRen_up. 2:rasimpl;reflexivity. eapply WellRen_up. 2:rasimpl;reflexivity. eauto using WellRen_weak, WellRen_S. }
    eauto using RwkWt, validity_ty_ctx.
  Qed.

  Lemma Pwk_conv_Pwk' : Γ ,, (ty n, A) ,, (prop, t2),, (ty n, Awk) ▹ M ⊢< Ax l > Pwk ≡ Pwk' : Sort l.
  Proof.
    unfold Pwk, Awk, Pwk'.
    eapply conv_ren; eauto using PwkWt, validity_ty_ctx.
    eapply WellRen_up. 2:rasimpl; reflexivity. eauto using WellRen_weak, WellRen_S.
  Qed.

  Lemma pwk_conv_pwk' : Γ ,, (ty n, A) ,, (prop, t2) ,, (ty n, Awk) ,, (Ru (ty n) l, (up_ren (S >> S)) ⋅ B) 
    ▹ M ⊢< l > pwk ≡ pwk' : (up_ren (up_ren (S >> S))) ⋅ P00.
  Proof.
    unfold pwk, pwk', Awk. eapply conv_ren; eauto using pwkWt, validity_ty_ctx.
    eapply WellRen_up. 2:rasimpl;reflexivity. eapply WellRen_up. 2:rasimpl;reflexivity. eauto using WellRen_weak, WellRen_S.
  Qed.

  Lemma t0_conv_t0' : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< prop > t0 ≡ t0' : acc (ty n) Awk Rwk (var 1).
  Proof.
    unfold t0, t0'.
    econstructor; eauto using AwkWt, Awk_conv_Awk', Pwk_conv_Pwk', Rwk_conv_Rwk'.
    - eapply conv_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - eapply conv_ren; eauto using WellRen_weak, WellRen_S, AwkWt, validity_ty_ctx.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. 1:unfold Awk; rasimpl; reflexivity.
    - econstructor; eauto using AwkWt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:unfold Rwk, t2; rasimpl; simpl; reflexivity.
  Qed.

  Lemma t1_conv_t1' : Γ ,, (ty n, A) ,, (prop, t2) ▹ M ⊢< l > t1 ≡ t1' : Pwk <[ (var 1) .. ].
  Proof.
    unfold t1, t1'.
    econstructor; eauto using AwkWt, RwkWt, PwkWt, t0Wt, Awk_conv_Awk', Rwk_conv_Rwk', Pwk_conv_Pwk', t0_conv_t0'.
    - eassert (Pi _ l (S ⋅ Awk) (Pi prop l ((1 .: (0 .: S >> S)) ⋅ Rwk) ((1 .: (S >> S) >> S) ⋅ Pwk)) = (up_ren (S >> S)) ⋅ B).
      1: {unfold B, Awk, Rwk, Pwk, R0, P0. rasimpl. reflexivity. }
      rewrite H. eapply meta_conv_conv.
      1: eapply pwk_conv_pwk'. unfold P00, Pwk; rasimpl; reflexivity.
    - econstructor; eauto using t0Wt, validity_ty_ctx. eapply varty_meta. 1:econstructor. 1:econstructor. unfold Awk; rasimpl; reflexivity.
    - eapply pre_conv_in_ctx_ty. 1:eapply t0Wt; eauto. 
      1:eauto using pre_conv_in_ctx_ty,Γ_A_SA_conv, Γ_A_SA'.
      all:eauto using typing, conversion, pre_conv_in_ctx_ty,Γ_A_SA_conv, Γ_A_SA'.
      2:econstructor; eauto using t2Wt, validity_ty_ctx.
      1:eapply pre_conv_in_ctx_ty. 1:eapply PWt. 1,2:econstructor;eauto using validity_ty_ctx, conv_sym, ctx_conv_refl.
      econstructor.
      1:econstructor.
      all:eauto using validity_ty_ctx, conv_sym, ctx_conv_refl.
      eapply t2_conv_t2'.
  Qed.

  Lemma t3_conv_t3' : Γ ,, (ty n, A) ▹ M ⊢< l > t3 ≡ t3' : Pi prop l t2 P00.
  Proof.
    unfold t3, t3'. eapply meta_lvl_conv.
    1:econstructor; eauto using t2_conv_t2', t2Wt, P00_conv_P00'2.
    1:eapply meta_conv_conv. 1:eapply t1_conv_t1'.
    1:unfold Pwk, P00; substify; ssimpl; reflexivity.
    destruct l; eauto.
  Qed.

  Lemma t4_conv_t4' : Γ ,, (ty n, A) ▹ M ⊢< Ax l > t4 ≡ t4' : Sort l.
  Proof.
    unfold t4, t4'. eapply meta_conv_conv. 1:eapply meta_lvl_conv.
    1:econstructor; eauto using t2Wt, P00Wt2, t2_conv_t2', P00_conv_P00'2.
    all:destruct l; reflexivity.
  Qed.

  Lemma t5_conv_t5' : Γ ▹ M ⊢< Ru (ty n) l > t5 ≡ t5' : Pi (ty n) l A t4.
  Proof.
    unfold t5, t5'. econstructor; eauto using t3_conv_t3', t4_conv_t4'.
  Qed.


End AccCompValidityConv.

Lemma meta_tm_conv M Γ l t t' A : 
  Γ ▹ M ⊢< l > t : A ->
  t = t' ->
  Γ ▹ M ⊢< l > t' : A.
Proof.
  intros. subst. eauto.
Qed.



Lemma meta_tm_conv_conv M Γ l t t' u u' A :
  Γ ▹ M ⊢< l > t ≡ u : A ->
  t = t' ->
  u = u' ->
  Γ ▹ M ⊢< l > t' ≡ u' : A.
Proof.
  intros. subst. eauto.
Qed.

Lemma meta_ctx M Γ l t A Γ' : 
  Γ ▹ M ⊢< l > t : A ->
  Γ = Γ' ->
  Γ' ▹ M ⊢< l > t : A.
Proof.
  intros. subst. eauto.
Qed.

Lemma meta_ctx_conv M Γ Γ' Δ Δ' : 
  ▹ M ⊢ Γ ≡ Δ ->
  Γ = Γ' ->
  Δ = Δ' ->
  ▹ M ⊢ Γ' ≡ Δ'.
Proof.
  intros. subst. eauto.
Qed.


Lemma validity_gen M :
  (∀ Γ l t A,
    Γ ▹ M ⊢< l > t : A →
    Γ ▹ M ⊢< Ax l > A : Sort l
  ) ∧
  (∀ Γ l u v A,
    Γ ▹ M ⊢< l > u ≡ v : A →
    Γ ▹ M ⊢< l > u : A ∧ Γ ▹ M ⊢< l > v : A).
Proof.
  apply typing_mutind.
  all: try solve [ intros ; econstructor ; eauto using validity_ty_ctx, validity_conv_ctx].
  all: try solve [
    intros ; try econstructor ; try econstructor ; intuition eauto using validity_ty_ctx, validity_conv_ctx
  ].
  all:try solve [ intros ; intuition eauto 6 using conversion, typing].
  all: try solve [ intuition eauto using subst_ty, subst_one, validity_ty_ctx, conversion, typing, validity_ty_ctx, subst_one, valid_varty].
  all:intros.
  - eapply typing_conversion_ren in t as temp; eauto. 2:econstructor. Unshelve. 2:exact (fun _ => 0).
    rewrite closed_ren in temp; eauto using typing_closed.
  - eapply meta_lvl. 1:eapply type_sort. all:eauto.
  - intuition eauto. 1:econstructor; eauto.
    1:eapply subst_ty; eauto using subst_one, validity_ty_ctx.
    1:econstructor; eauto.
    eapply subst_ty; eauto using validity_ty_ctx.
    2:unfold P''; rasimpl; reflexivity.
    econstructor. 1:econstructor.
    + ssimpl. eapply subst_id; eauto using validity_ty_ctx.
    + ssimpl. eauto.
    + ssimpl. unfold B. rasimpl.
      eapply meta_tm_conv. 1:eapply meta_conv.
      1: eapply t5Wt; eauto.
      * unfold R', P'. ssimpl. f_equal. f_equal. substify. ssimpl. reflexivity.
      * unfold t10, t9, t8, t7. f_equal.
  - econstructor. 1:eapply type_sort; eauto using validity_ty_ctx.
    all:eapply subst_ty; eauto.
    all:eauto using validity_ty_ctx, subst_one.
    eapply subst_one; eauto.
    unfold a1. eapply type_cast; eauto.
    eapply type_injpi1; eauto.
  - split ; econstructor. all: intuition eauto.
    eapply pre_conv_in_ctx_ty. all: eauto using ctx_typing, validity_ty_ctx, ctx_conv_refl, conv_ccons, conv_sym.
  - split.
    + econstructor. all: intuition eauto.
    + econstructor.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 9 using pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply pre_conv_in_ctx_ty.
        - eapply type_conv. all: intuition eauto.
        - econstructor; eauto using validity_ty_ctx.
        - econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      }
      * apply conv_sym. constructor.
        all: intuition eauto.
  - split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. 1: intuition eauto.
        all: intuition eauto 8 using type_conv, pre_conv_in_ctx_ty, ctx_conv_refl, conv_ccons, conv_sym, ctx_typing, validity_ty_ctx.
        eapply type_conv. 1: intuition eauto.
        constructor. all: intuition eauto.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_ty_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto using subst_one.
            - intuition eauto.
          }
          reflexivity.
      }
  - split.
    + econstructor. all: intuition eauto.
    + eapply type_conv.
      * {
        econstructor. all: intuition eauto.
        - eapply type_conv. 1: intuition eauto.
          eapply meta_conv_conv.
          + eapply typing_conversion_subst. 1,2: intuition eauto using validity_ty_ctx.
            eapply well_scons_alt.
            * apply subst_id. eauto using validity_ty_ctx.
            * cbn. constructor. eauto using validity_ty_ctx.
          + reflexivity.
        - eapply pre_conv_in_ctx_ty.
          + eapply type_conv. 1: intuition eauto.
            eapply meta_conv_conv.
            * {
              eapply typing_conversion_subst. 1: intuition eauto.
              1:econstructor; eauto using validity_ty_ctx.
              eapply well_scons_alt.
              - change (↑ >> (↑ >> var)) with (var >> ren_term S >> ren_term S).
                eapply WellSubst_weak.
                1:eapply WellSubst_weak.
                1:apply subst_id; eauto using validity_ty_ctx.
                1,2:eauto using typing, validity_ty_ctx.
              - cbn. constructor.
                eapply meta_conv.
                + repeat constructor. all:eauto using validity_ty_ctx.
                + reflexivity.
            }
            * reflexivity.
          + constructor. 1: eauto using ctx_conv_refl, validity_ty_ctx. eauto.
          + econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.
      }
      * {
        apply conv_sym. eapply conv_trans.
        - eapply meta_conv_conv.
          + eapply typing_conversion_subst.
            all: intuition eauto using subst_one, validity_ty_ctx.
          + reflexivity.
        - eapply meta_conv_conv.
          { eapply conv_substs.
            - eauto using validity_conv_ctx.
            - eapply substs_one. eauto.
            - eapply subst_one. intuition eauto.
            - eapply subst_one. intuition eauto.
            - intuition eauto.
          }
          reflexivity.
      }
  - split; econstructor; intuition eauto using type_conv.
    eapply pre_conv_in_ctx_ty; eauto.
    1:econstructor. 1:econstructor. 
    4:econstructor. 4:econstructor.
    all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
    1:eapply type_ren; eauto using WellRen_S.
    2:eapply conv_ren; eauto using WellRen_S, conv_sym.
    all:econstructor; eauto using validity_ty_ctx.
  - assert (▹ M ⊢ (Γ,, (ty n, A')),, (ty n, S ⋅ A')).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      1:eapply type_ren; eauto using WellRen_S. econstructor; eauto using validity_ty_ctx. } 
    assert (▹ M ⊢ (Γ,, (ty n, A')),, (ty n, S ⋅ A') ≡ (Γ,, (ty n, A)),, (ty n, S ⋅ A)).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      eapply conv_ren; eauto using WellRen_S, conv_sym.
      econstructor; eauto using validity_ty_ctx. } 
    assert (▹ M ⊢ Γ,, (ty n, A)) by (econstructor; eauto using validity_ty_ctx).
    assert (Γ,, (ty n, A) ▹ M ⊢s (S ⋅ a .: (var 0 .: S >> var)) : (Γ,, (ty n, A)),, (ty n, S ⋅ A)).
    { intuition eauto. econstructor.
      2:ssimpl. 2:eapply type_ren; eauto.
      1:ssimpl; rewrite subst_id_reduce1; eapply subst_id; econstructor; eauto using validity_ty_ctx.
      1,2:rasimpl; eauto using WellRen_S. } 
    assert (Γ,, (ty n, A) ▹ M ⊢< Ax prop > RR : Sort prop).
    { intuition eauto. unfold RR. eapply subst_ty; eauto. } 
    assert (▹ M ⊢ (Γ,, (ty n, A)),, (prop, RR)).
    { econstructor; eauto. }
    split.
    1:econstructor.
    5:eapply type_conv. 5:econstructor.
    all: intuition eauto using type_conv.
    3:econstructor; eauto using conv_conv, conv_sym. 
    1:eapply pre_conv_in_ctx_ty; eauto.
    2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    eapply type_conv; eauto.
    eapply meta_lvl_conv. 1:econstructor.
    1,2:eauto.
    2:eauto.
    eapply meta_lvl_conv. 1:econstructor; eauto.
    1:unfold RR.
    1:eapply pre_subst_conv; eauto.
    1:rewrite subst_id_reduce1.
    1:eapply substs_one. 1:eapply conv_ren; eauto using WellRen_S.
    1:rewrite subst_id_reduce1.
    1:eapply subst_one. 1:eapply type_ren; eauto using WellRen_S.
    2:eauto.
    unfold acc_wk, A_wk, R_wk.
    econstructor.
    4:eapply meta_conv_conv.
    4:econstructor;eauto. 4:econstructor. 4:econstructor.
    4:rasimpl; eauto.
    1:eapply type_ren; eauto.
    2:eapply conv_ren; eauto.
    1,2:eapply WellRen_weak; eapply WellRen_S.
    eapply conv_ren; eauto.
    2:eapply WellRen_up. 2: eapply WellRen_up.
    2:eapply WellRen_weak; eapply WellRen_S.
    2,3:rasimpl;reflexivity.
    econstructor. 1:econstructor; eauto.
    1:eapply type_ren; eauto.
    1:eapply WellRen_weak, WellRen_S.
    rasimpl.
    eapply type_ren; eauto.
    1:econstructor; eauto.
    1:eapply type_ren; eauto. 1:eapply WellRen_weak, WellRen_S.
    eapply WellRen_weak. eapply WellRen_weak. eapply WellRen_S.
  - assert (▹ M ⊢ (Γ,, (ty n, A')),, (ty n, S ⋅ A')).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      1:eapply type_ren; eauto using WellRen_S. econstructor; eauto using validity_ty_ctx. } 
    assert (▹ M ⊢ (Γ,, (ty n, A')),, (ty n, S ⋅ A') ≡ (Γ,, (ty n, A)),, (ty n, S ⋅ A)).
    { intuition eauto. econstructor. 1:econstructor.
      all:eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
      eapply conv_ren; eauto using WellRen_S, conv_sym.
      econstructor; eauto using validity_ty_ctx. } 
    assert (▹ M ⊢ Γ,, (ty n, A)) by (econstructor; eauto using validity_ty_ctx).
    assert (Γ,, (ty n, A) ▹ M ⊢s (S ⋅ a .: (var 0 .: S >> var)) : (Γ,, (ty n, A)),, (ty n, S ⋅ A)).
    { intuition eauto. econstructor.
      2:ssimpl. 2:eapply type_ren; eauto.
      1:ssimpl; rewrite subst_id_reduce1; eapply subst_id; econstructor; eauto using validity_ty_ctx.
      1,2:rasimpl; eauto using WellRen_S. } 
    split.
    1:econstructor.
    5:eapply type_conv. 5:econstructor.
    all: intuition eauto using type_conv, conv_sym.
    eapply type_conv. 1:econstructor; eauto using type_conv.
    4:econstructor; eauto using conv_sym, conv_conv.
    2:eapply type_conv. 2:eauto.
    2:econstructor; eauto.
    1:eapply pre_conv_in_ctx_ty; eauto.
    2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    eapply type_conv; eauto.
    eapply pre_subst_conv; eauto using validity_ty_ctx.
    1:econstructor. 1:ssimpl. 1:eapply subst_one.
    2:rasimpl; simpl. 1,2:eauto.
    2:{
    econstructor. 1:ssimpl. 1:eapply subst_one.
    2:rasimpl; simpl. 1,2:eauto. }
    econstructor. 1:rasimpl; eapply substs_one.
    2:rasimpl;simpl. 1,2:eauto.
  - intuition eauto. 1:econstructor; eauto.
    eapply type_conv. 1:econstructor; eauto using type_conv.
    (* 4:eapply type_conv; eauto. 4:econstructor; eauto. *)
    4:eapply pre_subst_conv; eauto using validity_ty_ctx, conv_sym.
    4:eapply subst_one; eauto.
    4:eapply substs_one; eauto using conv_sym.
    2:eapply pre_conv_in_ctx_ty; eauto.
    1:eapply pre_conv_in_ctx_ty; eauto.
    1,2:econstructor.
    1,3,5,6:econstructor; eauto using conv_sym, validity_ty_ctx, ctx_conv_refl.
    1:eapply type_ren; eauto. 3:eapply conv_ren; eauto using conv_sym.
    1,3:econstructor; eauto using validity_ty_ctx.
    1,2:eapply WellRen_S.
    2:eapply subst_one; eauto.
    eapply type_conv. 1: eapply pre_conv_in_ctx_ty; eauto.
    * econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      1:eapply pre_conv_in_ctx_ty; eauto. 
      2:eauto using Γ_A_SA_conv. 1:eapply Γ_A_SA'; eauto.
      eapply pre_conv_in_ctx_ty; eauto.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using conv_sym, ctx_conv_refl ,validity_ty_ctx.
    * eapply meta_ctx_conv. 1:eapply Γ_A_B_conv. 3:exact c. 5:exact c0. 7:exact c1.
      all:eauto.
    * eapply pre_conv_in_ctx_conv.
      1:unfold P''. 1:eapply conv_ren; eauto.
      Unshelve. 5:exact ((Γ,, (ty n, A)),, (Ru (ty n) l, B)).
      1:eauto using validity_ty_ctx.
      1:econstructor. 
      1:ssimpl; eapply WellRen_weak, WellRen_S.
      1: ssimpl; eapply varty_meta.
      1:econstructor. 1:econstructor.
      1:rasimpl;reflexivity.
      2:eapply Γ_A_B_conv; eauto.
      econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      all:eapply pre_conv_in_ctx_ty.
      1,4:eauto.
      all:eauto using Γ_A_SA_conv, Γ_A_SA'.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.
  - destruct H0, H1, H2, H3, H4, H5. split.
    + eapply type_J; eauto.
    + eapply type_conv. 1:eapply type_J; eauto using type_conv, conv_obseq.
      1:eapply pre_conv_in_ctx_ty; eauto using ctx_typing, validity_ty_ctx, conv_ccons, ctx_conv_refl, conv_sym.
      1:eapply type_conv; eauto.
      1,2: eapply pre_subst_conv; eauto using subst_one, validity_ty_ctx, substs_one, conv_sym.
  (* - intuition eauto.
    1:econstructor.
    5: eapply type_conv. 5:econstructor.
    all:eauto using type_conv, conv_sym.
    eapply type_conv; eauto.
    econstructor; eauto using conversion, validity_ty_ctx. *)
  - intuition eauto.
    1:econstructor.
    6:eapply type_conv.
    6:econstructor.
    all:eauto.
    1,2:eapply pre_conv_in_ctx_ty; eauto.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    1:eapply type_conv; eauto.
    1,2:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
  - intuition eauto.
    1:econstructor.
    7:eapply type_conv.
    7:econstructor.
    all:eauto using conv_sym, type_conv.
    1,2:eapply pre_conv_in_ctx_ty; eauto.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    1:eapply type_conv; eauto.
    all:unfold a1.
    1,2:econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
    all:eapply pre_subst_conv; eauto using conv_sym, validity_ty_ctx, subst_one, substs_one.
    1:eapply subst_one.
    2:eapply substs_one.
    2: { eapply conv_conv. 1:econstructor; eauto using conv_sym, conv_conv.
    1:{ econstructor; eauto. 1,2:eapply pre_conv_in_ctx_ty; eauto using ctx_typing, validity_ty_ctx.
    1,2:econstructor; eauto using conv_sym, ctx_conv_refl, validity_ty_ctx.
    eapply type_conv; eauto.
    econstructor; eauto using conversion, validity_ty_ctx. }
    1: econstructor; eauto. 
    1:econstructor; eauto using conv_sym.  
    1,2:eapply pre_conv_in_ctx_conv; eauto using conv_sym.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.   
    1:eapply conv_conv; eauto using conv_sym.
    1:econstructor. 
    2,3:econstructor.
    all:eauto using conversion, validity_ty_ctx. }
    2:eapply subst_one; eauto using typing. 
    eapply type_conv.
    1:econstructor; eauto using type_conv. 2:eauto using conv_sym.
    econstructor; eauto.
    1,2:eapply pre_conv_in_ctx_ty; eauto using conv_sym.
    1-4:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
    eapply type_conv; eauto.
    econstructor; eauto using conv_sym, conversion, validity_ty_ctx.
  - intuition eauto using typing.
  eapply type_conv. 1:econstructor; eauto using type_conv.
    4:eapply type_conv; eauto. 4:econstructor; eauto.
    4:{
      econstructor; eauto.
      1:eapply pre_subst_conv; eauto using validity_ty_ctx, subst_one, substs_one, conv_sym.
      1:eapply conv_conv. 1:eapply conv_sym, conv_accel; eauto using conversion, typing.
      1:eapply pre_subst_conv; eauto using validity_ty_ctx, subst_one, substs_one, conv_sym.
      eapply conv_conv.
      1:eapply pre_subst_conv; eauto using validity_ty_ctx, conv_sym.
      3:{econstructor. 1:econstructor. 1:ssimpl; eauto using validity_ty_ctx, subst_id.
      all:asimpl. 1:eauto. eapply meta_conv. 1:eapply t5Wt. all:eauto.
      unfold B, R_, P_. rasimpl. substify. rasimpl. f_equal. f_equal. substify. ssimpl. reflexivity. }
      3:unfold P''; rasimpl.
      3:eapply pre_subst_conv; eauto using subst_one, validity_ty_ctx, conv_refl, substs_one.
      * econstructor. 1:econstructor. 1:ssimpl; eapply subst_id; eauto using validity_ty_ctx.
        all:ssimpl; eauto.
        eapply type_conv. 
        - eapply meta_tm_conv. 1:eapply t5Wt. 
          ** exact H9.
          ** eapply pre_conv_in_ctx_ty. 1:exact H10. 2:eapply Γ_A_SA_conv; eauto. eapply  Γ_A_SA'; eauto.
          ** eapply pre_conv_in_ctx_ty. 1:exact H11. 1:eauto using validity_ty_ctx, ctx_typing.
             econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
          ** eapply type_conv. 1:exact H13. eauto.
          ** eapply pre_conv_in_ctx_ty. 1:eapply type_conv. 1:exact H12.
             1:{ unfold P''. eapply conv_ren; eauto using validity_ty_ctx. econstructor. 
                1:ssimpl; eauto using WellRen_weak, WellRen_S. ssimpl. eapply varty_meta. 1:econstructor. 
                1:econstructor. rasimpl. reflexivity. }
              2:eapply Γ_A_B_conv; eauto.
              econstructor. 1:eauto using validity_ty_ctx, ctx_typing.
              eapply BWt; eauto.
              1,2:eapply pre_conv_in_ctx_ty; eauto.
              3:econstructor; eauto using validity_ty_ctx.
              3:econstructor; eauto using validity_ty_ctx, ctx_conv_refl, conv_sym.
              1:econstructor. 1:econstructor. 4:econstructor. 4:econstructor.
              all:eauto using conv_sym, validity_ty_ctx, ctx_conv_refl.
              1:eapply type_ren; eauto using ctx_typing, validity_ty_ctx.
              2:eapply conv_ren; eauto using ctx_typing, validity_ty_ctx, conv_sym.
              all:eapply WellRen_S. 
          ** eapply type_conv. 1:exact H14. econstructor; eauto.
          **  rasimpl. reflexivity.
        -  unfold B, P_, R_. rasimpl. eapply conv_sym. econstructor; eauto.
          eapply meta_conv_conv. 1:eapply meta_lvl_conv. 1:econstructor.
        4,5:reflexivity.
        ** eapply subst_ty; eauto using validity_ty_ctx. econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
        ** eapply pre_subst_conv; eauto using validity_ty_ctx, conv_refl.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx, refl_subst.
            ssimpl. eapply meta_conv_conv. 1:eapply conv_ren; eauto using validity_ty_ctx, WellRen_S, conv_refl. rasimpl. reflexivity.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
        ** substify. asimpl. eapply meta_tm_conv_conv. 1:renamify. 1:eapply P00_conv_P00'2; eauto using conv_sym.
           all:substify;asimpl;reflexivity.
      * econstructor. 1:econstructor. 1:ssimpl; eapply refl_subst, subst_id; eauto using validity_ty_ctx.
        all:ssimpl.
        1:eauto using conv_sym.
        eapply conv_sym. eapply conv_conv.
        1:{ unfold t7, t6, t5, t4, t3, t2, pwk, Pwk, Rwk, Awk, P'', B, P_, R_. eapply meta_tm_conv_conv. 1:eapply t5_conv_t5'.
            3:exact c. 5:exact c0. 7:exact c1. 12:exact c2. 10:exact c3. 13:exact c4.  all:eauto.
            rasimpl. reflexivity. }
        unfold B, P_, R_. rasimpl. econstructor; eauto using conv_refl.
        eapply meta_conv_conv. 1:eapply meta_lvl_conv. 1:econstructor.
        4,5:reflexivity.
        ** eapply subst_ty; eauto using validity_ty_ctx. econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
        ** eapply pre_subst_conv; eauto using validity_ty_ctx, conv_refl.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx, refl_subst.
            ssimpl. eapply meta_conv_conv. 1:eapply conv_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
          *** econstructor. 1:ssimpl. 1:rewrite subst_id_reduce1. 1:eauto using subst_id, validity_ty_ctx.
            ssimpl. eapply meta_conv. 1:eapply type_ren; eauto using validity_ty_ctx, WellRen_S. rasimpl. reflexivity.
        ** substify. asimpl. eapply conv_refl.  
          eapply meta_tm_conv. 1: eapply meta_ctx.  1:eapply P00Wt2. 1:exact H8. 1:exact H2. 1:exact H3. 1:exact H5. 1:exact H4.
          1:exact H6. 1:rasimpl; reflexivity. substify. asimpl. reflexivity. }
           
    2:eapply pre_conv_in_ctx_ty; eauto.
    1:eapply pre_conv_in_ctx_ty; eauto.
    1,2:econstructor.
    1,3,5,6:econstructor; eauto using conv_sym, validity_ty_ctx, ctx_conv_refl.
    1:eapply type_ren; eauto. 3:eapply conv_ren; eauto using conv_sym.
    1,3:econstructor; eauto using validity_ty_ctx.
    1,2:eapply WellRen_S.
    eapply type_conv. 1: eapply pre_conv_in_ctx_ty; eauto.
    * econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      1:eapply pre_conv_in_ctx_ty; eauto.
      2:eauto using Γ_A_SA_conv. 1:eapply Γ_A_SA'; eauto.
      eapply pre_conv_in_ctx_ty; eauto.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using conv_sym, ctx_conv_refl ,validity_ty_ctx.
    * eapply meta_ctx_conv. 1:eapply Γ_A_B_conv. 3:exact c. 5:exact c0. 7:exact c1.
      all:eauto.
    * eapply pre_conv_in_ctx_conv.
      1:unfold P''. 1:eapply conv_ren; eauto.
      Unshelve. 5:exact ((Γ,, ((ty n), A)),, (Ru (ty n) (ty m), B)).
      1:eauto using validity_ty_ctx.
      1:econstructor.
      1:ssimpl; eapply WellRen_weak, WellRen_S.
      1: ssimpl; eapply varty_meta.
      1:econstructor. 1:econstructor.
      1:rasimpl;reflexivity.
      2:eapply Γ_A_B_conv; eauto.
      econstructor. 1:econstructor; eauto using validity_ty_ctx.
      eapply BWt; eauto.
      all:eapply pre_conv_in_ctx_ty.
      1,4:eauto.
      all:eauto using Γ_A_SA_conv, Γ_A_SA'.
      1:econstructor; eauto using validity_ty_ctx.
      econstructor; eauto using ctx_conv_refl, conv_sym, validity_ty_ctx.      
  - intuition eauto. 
    * econstructor. 
      1,2:econstructor; eauto.
      all: eauto.
    * unfold t8.
      econstructor; eauto.
      unfold t7.
      assert (Γ ,, (i, A2) ▹ M ⊢< i > t5 : S ⋅ A1).
      { unfold t5. unfold A1'.
        econstructor. 
        ** unfold A2'. eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx. 
        ** eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** econstructor.
           1-4:eapply type_ren; eauto using WellRen_S.
           1,2,4,5:econstructor; eauto using validity_ty_ctx.
           1,2:eapply type_ren; eauto using WellRen_S.
           1,2:econstructor; eauto using validity_ty_ctx.
           1,2:eapply WellRen_up; eauto using WellRen_S.
           eapply type_ren; eauto using WellRen_S.
           econstructor; eauto using validity_ty_ctx.
        ** eapply meta_conv. 1:econstructor. 2:econstructor.           
           1:econstructor; eauto using validity_ty_ctx.
           unfold A2'; eauto. } 
      econstructor; eauto.
      1:eapply subst_ty; eauto.
      1:econstructor; eauto using validity_ty_ctx.
      1:econstructor. 2:ssimpl; renamify; eauto.
      
      1:ssimpl. 
      3: {  unfold t6. 1:eapply meta_conv.
        1:econstructor; eauto. 4:unfold B1'; rasimpl; reflexivity.
        1,2:unfold A1', B1'.
        all:eapply type_ren; eauto using WellRen_S.
        1,2,4:econstructor; eauto using validity_ty_ctx.
        1:eapply type_ren; eauto using WellRen_S.
        1:econstructor; eauto using validity_ty_ctx.
        eapply WellRen_up; eauto using WellRen_S. }
      2:{ eapply meta_conv.
       1:econstructor.
       7:unfold B1', t5; rasimpl.
       7:f_equal. 7:unfold B2';rasimpl.
       7:setoid_rewrite subst_id_reduce1; rasimpl; reflexivity.
       6:eapply meta_conv. 6:econstructor. 7:econstructor.
       6:econstructor; eauto using validity_ty_ctx. 6:unfold A2'; reflexivity.
       all:unfold A1', B1'.
       all:eapply type_ren; eauto using WellRen_S.
       3,6:eapply WellRen_up; eauto.
       3,4:eapply WellRen_S.
       2,4:econstructor.
       3,5:unfold A2'; eapply type_ren; eauto using WellRen_S.
       all:econstructor; eauto using validity_ty_ctx. } 

      change (S >> var) with (var >> ren_term S).
      eapply WellSubst_weak; eauto using subst_id, validity_ty_ctx.
  - split.
    + econstructor. all: intuition eauto.
      econstructor. auto.
    + eapply meta_conv.
      { eapply typing_conversion_subst.
        - eauto using validity_ty_ctx.
        - eauto using validity_ty_ctx.
        - eapply well_scons_alt.
          + apply subst_one. assumption.
          + econstructor. all: intuition eauto.
      }
      rasimpl. reflexivity.
  - intuition eauto. 1:econstructor; eauto. 
    eapply subst_ty; eauto using validity_ty_ctx.
    2:unfold P''; rasimpl; reflexivity.
    econstructor. 1:econstructor.
    + ssimpl. eapply subst_id; eauto using validity_ty_ctx.
    + ssimpl. eauto.
    + ssimpl. unfold B. rasimpl.
      eapply meta_tm_conv. 1:eapply meta_conv.
      1: eapply t5Wt; eauto.
      * unfold R', P'. ssimpl. f_equal. f_equal. substify. ssimpl. reflexivity.
      * unfold t10, t9, t8, t7. f_equal. 
Qed.

Theorem validity_conv_left M Γ l t u A :
  Γ ▹ M ⊢< l > t ≡ u : A ->
  Γ ▹ M ⊢< l > t : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_conv_right M Γ l t u A :
  Γ ▹ M ⊢< l > t ≡ u : A ->
  Γ ▹ M ⊢< l > u : A.
Proof.
  intros. eapply validity_gen in H as (H1 & H2); eauto.
Qed.

Theorem validity_ty_ty M Γ l t A :
  Γ ▹ M ⊢< l > t : A ->
  Γ ▹ M ⊢< Ax l > A : Sort l.
Proof.
  intros.
  eapply validity_gen in H. assumption.
Qed.

Lemma validity_subst_conv_left M Δ Γ σ τ :
  Δ ▹ M ⊢s σ ≡ τ : Γ ->
  Δ ▹ M ⊢s σ : Γ.
Proof.
  intros. induction H; eauto using validity_conv_left, WellSubst.
Qed.

Lemma subst_sym M Δ Γ σ τ :
  ▹ M ⊢ Δ ->
  ▹ M ⊢ Γ ->
  Δ ▹ M ⊢s σ ≡ τ : Γ ->
  Δ ▹ M ⊢s τ ≡ σ : Γ.
Proof.
  intros. induction H1; eauto using ConvSubst.
  econstructor; dependent destruction H0; eauto.
  eapply conv_sym. eapply conv_conv. 1:eauto.
  eapply conv_substs in H1; eauto using validity_subst_conv_left.
  eauto.
Qed.


Lemma validity_subst_conv_right M Δ Γ σ τ :
  ▹ M ⊢ Δ ->
  ▹ M ⊢ Γ ->
  Δ ▹ M ⊢s σ ≡ τ : Γ ->
  Δ ▹ M ⊢s τ : Γ.
Proof.
  intros. eapply subst_sym in H1; eauto. eapply validity_subst_conv_left; eauto.
Qed.




Theorem subst_conv M Γ l t u A Δ σ τ A' :
  ▹ M ⊢ Δ ->
  Δ ▹ M ⊢s σ ≡ τ : Γ ->
  Γ ▹ M ⊢< l > t ≡ u : A ->
  A' = A <[ σ ] ->
  Δ ▹ M ⊢< l > t <[ σ ] ≡ u <[ τ ] : A'.
Proof.
  intros.
  eauto 8 using pre_subst_conv, validity_conv_left, validity_conv_right, validity_subst_conv_left, validity_subst_conv_right, validity_ty_ctx.
Qed.


Lemma validity_ctx_conv_left M Γ Δ :
  ▹ M ⊢ Γ ≡ Δ ->
  ▹ M ⊢ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto using validity_conv_left.
Qed.


Lemma ctx_conv_sym M Γ Δ :
  ▹ M ⊢ Γ ≡ Δ ->
  ▹ M ⊢ Δ ≡ Γ.
Proof.
  intros. induction H.
  - econstructor.
  - econstructor; eauto.
    eapply conv_sym in H0.
    eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_left.
Qed.


Lemma validity_ctx_conv_right M Γ Δ :
  ▹ M ⊢ Γ ≡ Δ ->
  ▹ M ⊢ Δ.
Proof.
  intros. eauto using ctx_conv_sym, validity_ctx_conv_left.
Qed.



Theorem conv_in_ctx_ty M Γ Δ l t A :
  ▹ M ⊢ Γ ≡ Δ ->
  Γ ▹ M ⊢< l > t : A ->
  Δ ▹ M ⊢< l > t : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_ty; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.

Theorem conv_in_ctx_conv M Γ Δ l t u A :
  ▹ M ⊢ Γ ≡ Δ ->
  Γ ▹ M ⊢< l > t ≡ u : A ->
  Δ ▹ M ⊢< l > t ≡ u : A.
Proof.
  intros.
  eapply pre_conv_in_ctx_conv; eauto using validity_ctx_conv_right, ctx_conv_sym.
Qed.


(* type inversion *)
Inductive type_inv_data M : ctx -> level -> term -> term -> Prop :=
  | inv_data_var Γ l x A T
    (var_in_ctx : Γ ∋< l > x : A)
    (conv_ty : Γ ▹ M ⊢< Ax l > T ≡ A : Sort l)
    : type_inv_data M Γ l (var x) T
  | inv_data_sort Γ l i T
    (lvl_eq : l = Ax (Ax i))
    (conv_ty : Γ ▹ M ⊢< Ax (Ax (Ax i)) > T ≡ Sort (Ax i) : Sort (Ax (Ax i)))
    : type_inv_data M Γ l (Sort i) T
  | inv_data_assm Γ c A l T 
    (assm_in_sig : nth_error assm_sig c = Some A)
    (A_Wt : ∙ ▹ M ⊢< Ax prop > A : Sort prop)
    (lvl_eq : l = prop)
    (conv_ty : Γ ▹ M ⊢< Ax prop > T ≡ A : Sort prop)
    : type_inv_data M Γ l (assm c) T
  | inv_data_pi Γ l A B i j T
    (A_Wt : Γ ▹ M ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ▹ M ⊢< Ax j > B : Sort j)
    (lvl_eq : l = Ax (Ru i j))
    (conv_ty : Γ ▹ M ⊢< Ax (Ax (Ru i j)) > T ≡ Sort (Ru i j) : Sort (Ax (Ru i j)))
    : type_inv_data M Γ l (Pi i j A B) T
  | inv_data_lam Γ l A B t i j T
    (A_Wt : Γ ▹ M ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ▹ M ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ,, (i , A) ▹ M ⊢< j > t : B)
    (lvl_eq : l = Ru i j)
    (conv_ty : Γ ▹ M ⊢< Ax (Ru i j) > T ≡ Pi i j A B : Sort (Ru i j))
    : type_inv_data M Γ l (lam i j A B t) T
  | inv_data_app Γ A B t u i j T l
    (A_Wt : Γ ▹ M ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ,, (i, A) ▹ M ⊢< Ax j > B : Sort j)
    (t_Wt : Γ ▹ M ⊢< Ru i j > t : Pi i j A B)
    (u_Wt : Γ ▹ M ⊢< i > u : A)
    (lvl_eq : l = j)
    (conv_ty : Γ ▹ M ⊢< Ax j > T ≡ B <[ u.. ] : Sort j)
    : type_inv_data M Γ l (app i j A B t u) T
  | inv_data_Nat Γ l T
    (lvl_eq : l = ty 1)
    (conv_ty : Γ ▹ M ⊢< ty 2 > T ≡ Sort (ty 0) : Sort (ty 1))
    : type_inv_data M Γ l Nat T
  | inv_data_zero l Γ T
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ▹ M ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data M Γ l zero T
  | inv_data_succ Γ l t T
    (t_Wt : Γ ▹ M ⊢< ty 0 > t : Nat)
    (lvl_eq : l = ty 0)
    (conv_ty : Γ ▹ M ⊢< ty 1 > T ≡ Nat : Sort (ty 0))
    : type_inv_data M Γ l (succ t) T
  | inv_data_rec Γ l i P p_zero p_succ t T
    (P_Wt : Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax i > P : Sort i)
    (p_zero_Wt : Γ ▹ M ⊢< i > p_zero : P <[ zero .. ])
    (p_succ_Wt : Γ ,, (ty 0 , Nat) ,, (i , P) ▹ M ⊢< i > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ])
    (t_Wt : Γ ▹ M ⊢< ty 0 > t : Nat)
    (lvl_eq : l = i)
    (conv_ty : Γ ▹ M ⊢< Ax i > T ≡ P <[ t.. ] : Sort i)
    : type_inv_data M Γ l (rec i P p_zero p_succ t) T
  | inv_data_acc Γ n A R a l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (lvl_eq : l = Ax prop)
    (conv_ty : Γ ▹ M ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data M Γ l (acc (ty n) A R a) T
  | inv_data_accin Γ n A R a p l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (B_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (A_wk := (S >> S) ⋅ A)
    (R_wk := (up_ren (up_ren (S >> S))) ⋅ R)
    (acc_wk := acc (ty n) A_wk R_wk (var 1) )
    (R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))])
    (p_Wt : Γ ▹ M ⊢< prop > p : Pi (ty n) prop A (Pi prop prop R' acc_wk))
    (lvl_eq : l = prop)
    (conv_ty : Γ ▹ M ⊢< Ax prop > T ≡ acc (ty n) A R a : Sort prop)
    : type_inv_data M Γ l (accin (ty n) A R a p) T
  | inv_data_accinv Γ n A R a p b r l T 
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (p_Wt : Γ ▹ M ⊢< prop > p : acc (ty n) A R a)
    (b_Wt : Γ ▹ M ⊢< ty n > b : A)
    (r_Wt : Γ ▹ M ⊢< prop > r : R <[a.:b..])
    (lvl_eq : l = prop)
    (conv_ty : Γ ▹ M ⊢< Ax prop > T ≡ acc (ty n) A R b : Sort prop)
    : type_inv_data M Γ l (accinv (ty n) A R a p b r) T
  | inv_data_accel Γ n l A R a q P p T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (P_Wt : Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l)
    (R' := (1 .: (0 .: (S >> S))) ⋅ R)
    (P' := (1 .: (S >> S >> S)) ⋅ P)
    (B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P'))
    (P'' := (1.: (S >> S)) ⋅ P)
    (p_Wt : Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p : P'')
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (q_Wt : Γ ▹ M ⊢< prop > q : acc (ty n) A R a)
    (conv_ty : Γ ▹ M ⊢< Ax l > T ≡ P <[a ..] : Sort l)
    : type_inv_data M Γ l (accel (ty n) l A R P p a q) T
  | inv_data_accelcomp Γ n m A R a q P p l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (R_Wt : Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop)
    (P_Wt : Γ ,, (ty n, A) ▹ M ⊢< Ax (ty m) > P : Sort (ty m))
    (R' := (1 .: (0 .: (S >> S))) ⋅ R)
    (P' := (1 .: (S >> S >> S)) ⋅ P)
    (B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R' P'))
    (P'' := (1.: (S >> S)) ⋅ P)
    (p_Wt : Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ▹ M ⊢< ty m > p : P'')
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (q_Wt : Γ ▹ M ⊢< prop > q : acc (ty n) A R a)
    (Awk := (S >> S) ⋅ A)
    (Rwk := (up_ren (up_ren (S >> S))) ⋅ R)
    (Pwk := (up_ren (S >> S)) ⋅ P)
    (pwk := (up_ren (up_ren (S >> S))) ⋅ p)
    (t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0))
    (t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0)
    (t2 := R<[S ⋅ a .: (var 0 .: S >> var)])
    (t3 := lam prop (ty m) t2 P'' t1)
    (t4 := Pi prop (ty m) t2 P'')
    (t5 := lam (ty n) (ty m) A t4 t3)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax prop > T ≡
         obseq (ty m) (P <[a ..])
           (accel (ty n) (ty m) A R P p a q)
           (p <[ t5 .: a ..]) : Sort prop)
    : type_inv_data M Γ l (accelcomp (ty n) (ty m) A R P p a q) T

  | inv_data_obseq Γ n A a b l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (b_Wt : Γ ▹ M ⊢< ty n > b : A)
    (lvl_eq : l = Ax prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax (Ax prop) > T ≡ Sort prop : Sort (Ax prop))
    : type_inv_data M Γ l (obseq (ty n) A a b) T

  | inv_data_obsrefl Γ n A a l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax prop > T ≡ obseq (ty n) A a a : Sort prop)
    : type_inv_data M Γ l (obsrefl (ty n) A a) T

  | inv_data_J Γ n A a P p b e l T
    (A_Wt : Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n))
    (a_Wt : Γ ▹ M ⊢< ty n > a : A)
    (P_Wt : Γ ,, (ty n , A) ▹ M ⊢< Ax prop > P : Sort prop)
    (p_Wt : Γ ▹ M ⊢< prop > p : P <[a..])
    (b_Wt : Γ ▹ M ⊢< ty n > b : A)
    (e_Wt : Γ ▹ M ⊢< prop > e : obseq (ty n) A a b)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax prop > T ≡ P <[b..] : Sort prop)
    : type_inv_data M Γ l (J (ty n) A a P p b e) T

  | inv_data_cast Γ i A B e a l T
    (A_Wt : Γ ▹ M ⊢< Ax i > A : Sort i)
    (B_Wt : Γ ▹ M ⊢< Ax i > B : Sort i)
    (e_Wt : Γ ▹ M ⊢< prop > e : obseq (Ax i) (Sort i) A B)
    (a_Wt : Γ ▹ M ⊢< i > a : A)
    (lvl_eq : l = i)
    (conv_ty :
       Γ ▹ M ⊢< Ax i > T ≡ B : Sort i)
    : type_inv_data M Γ l (cast i A B e a) T

  | inv_data_injpi1 Γ i n A1 A2 B1 B2 e l T
    (A1_Wt : Γ ▹ M ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ▹ M ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ▹ M ⊢< prop >
         e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax prop > T ≡ obseq (Ax i) (Sort i) A2 A1 : Sort prop)
    : type_inv_data M Γ l (injpi1 i (ty n) A1 A2 B1 B2 e) T

  | inv_data_injpi2 Γ i n A1 A2 B1 B2 e a2 l T
    (A1_Wt : Γ ▹ M ⊢< Ax i > A1 : Sort i)
    (B1_Wt : Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 : Sort (ty n))
    (A2_Wt : Γ ▹ M ⊢< Ax i > A2 : Sort i)
    (B2_Wt : Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 : Sort (ty n))
    (e_Wt :
       Γ ▹ M ⊢< prop >
         e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n)))
             (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2))
    (a2_Wt : Γ ▹ M ⊢< i > a2 : A2)
    (a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2)
    (lvl_eq : l = prop)
    (conv_ty :
       Γ ▹ M ⊢< Ax prop > T ≡
         obseq (Ax (ty n)) (Sort (ty n))
           (B1<[ a1 ..]) (B2<[a2..]) : Sort prop)
    : type_inv_data M Γ l (injpi2 i (ty n) A1 A2 B1 B2 e a2) T.


Derive Signature for type_inv_data.


Lemma type_inv M Γ l t T :
  Γ ▹ M ⊢< l > t : T ->
  type_inv_data M Γ l t T.
Proof.
  intros.
  apply validity_ty_ty in H as T_Wt.
  induction H. 1-21:econstructor; eauto using conv_refl.
  eapply validity_conv_left in H0 as AWt.
  eapply IHtyping in AWt as IH.
  depelim IH; econstructor; subst; eauto using conv_sym, conv_trans.
Qed.


(* composite lemmas, for helping automation *)

Lemma conv_ty_in_ctx_conv  M Γ l A A' l' t u B :
  Γ ,, (l , A) ▹ M ⊢< l' > t ≡ u : B ->
  Γ ▹ M ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ▹ M ⊢< l' > t ≡ u : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_conv; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.


Lemma conv_ty_in_ctx_ty  M Γ l A A' l' t B :
  Γ ,, (l , A) ▹ M ⊢< l' > t : B ->
  Γ ▹ M ⊢< Ax l > A ≡ A' : Sort l ->
  Γ ,, (l , A') ▹ M ⊢< l' > t : B.
Proof.
  intros t_eq_u A_eq_A'.
  eapply conv_in_ctx_ty; eauto.
  apply conv_ccons; eauto using ctx_conv_refl, validity_ty_ctx, validity_conv_left.
Qed.

(* the following lemma helps  automation to type some substitutions that appear often in the proof *)
Lemma subst_id_var1  M Γ l P :
  Γ ,, (ty 0, Nat) ▹ M ⊢< Ax l > P : Sort l ->
  (Γ,, (ty 0, Nat)),, (l, P) ▹ M ⊢s (succ (var 1) .: ↑ >> (↑ >> var)) : Γ ,, (ty 0, Nat).
Proof.
  intro H.
  apply well_scons.
  - ssimpl.
    change (↑ >> (↑ >> var)) with ((var >> ren_term ↑) >> ren_term ↑).
    eapply WellSubst_weak; eauto.
    eapply validity_ty_ctx in H. dependent destruction H.
    eapply WellSubst_weak; eauto using subst_id.
  - ssimpl. apply type_succ. apply (type_var _ _ 1 _ Nat); eauto.
    all:eauto using validity_ty_ctx, ctx_cons.
    eapply (vartyS _ _ _ Nat _ 0). eapply vartyO.
Qed.


Lemma type_app' M  Γ i j A B t u T :
      Γ ▹ M ⊢< Ru i j > t : Pi i j A B →
      Γ ▹ M ⊢< i > u : A →
      (Γ ▹ M ⊢< Ax j > B <[ u .. ] : Sort j → Γ ▹ M ⊢< Ax j > T ≡ B <[ u .. ] : Sort j) →
      Γ ▹ M ⊢< j > app i j A B  t u : T.
Proof.
  intros.
  eapply validity_ty_ty in H as temp.
  eapply type_inv in temp. dependent destruction temp.
  assert (Γ ▹ M ⊢< j > app i j A B t u : B<[u..]) as H2 by eauto using type_app.
  eapply type_conv.
  1: eauto.
  eapply conv_sym. eapply validity_ty_ty in H2. eauto.
Qed.

Lemma conv_app' M  Γ i j A B_ B t u A' B' t' u' :
  Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
  Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B': Sort j →
  Γ ▹ M ⊢< Ru i j > t ≡ t' : Pi i j A B →
  Γ ▹ M ⊢< i > u ≡ u' : A →
  B_ = B <[ u .. ] →
  Γ ▹ M ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B_.
Proof.
  intros. subst. eapply conv_app. all: eauto using validity_conv_left, validity_conv_right, type_conv.
Qed.

Lemma conv_pi' M  Γ i j l A B A' B' :
  Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
  Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B' : Sort j →
  l = Ru i j →
  Γ ▹ M ⊢< Ax l > Pi i j A B ≡ Pi i j A' B' : Sort l.
Proof.
  intros. subst. eapply conv_pi. all: eauto.
  eapply validity_conv_left. all: eassumption.
Qed.

Lemma conv_var' M  Γ x l A T :
      Γ ∋< l > x : A →
      ▹ M ⊢ Γ →
      T = A →
      Γ ▹ M ⊢< l > (var x) ≡ (var x) : T.
Proof.
  intros. subst. eauto using conv_var.
Qed.


Lemma conv_lam' M  Γ i j A B t A' B' t' l T:
      Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ▹ M ⊢< j > t ≡ t' : B →
      l = Ru i j →
      T = Pi i j A B →
      Γ ▹ M ⊢< l > lam i j A B t ≡ lam i j A' B' t' : T.
Proof.
  intros. subst. eapply conv_lam. all: eauto.
  eapply validity_conv_left. all: eassumption.
Qed.

Lemma conv_sort' M  l l' Γ T :
      ▹ M ⊢ Γ →
      T = Sort (Ax l) →
      l' = Ax (Ax l) →
      Γ ▹ M ⊢< l' > Sort l ≡ Sort l : T.
Proof.
  intros. subst. eauto using conv_sort.
Qed.




Lemma lift_subst  M σ1 σ2 i A A' Γ:
    ▹ M ⊢ Γ ,, (i, A) →
    ∙ ▹ M ⊢s σ1 ≡ σ2 : Γ →
    A' = A <[ σ1] →
    ∙ ,, (i, A') ▹ M ⊢s ((var 0) .: (σ1 >> ren_term S)) ≡ ((var 0) .: (σ2 >> ren_term S)) : (Γ ,, (i, A)).
Proof.
    intros. subst. dependent destruction H. eapply conv_scons.
    1:ssimpl. 1:eapply ConvSubst_weak; eauto.
    1:eapply subst_ty; eauto using validity_subst_conv_left, ctx_typing.
    rasimpl. assert (A <[ σ1 >> ren_term S] = (plus (S 0)) ⋅ (A <[ σ1])). 1:simpl. 1:ssimpl. 1:eauto.
    rewrite H2.
    eapply conv_var. 1:eauto. 1:inversion H.
    1:eapply validity_subst_conv_left in H0.
    1:econstructor. 1:econstructor. 1:econstructor. 1:econstructor.
    eapply subst_ty; eauto using validity_subst_conv_left. econstructor.
Qed.


Lemma lift_subst2  M σ1 σ2 i j B A _A _B Γ:
    ▹ M ⊢ Γ ,, (i, A) ,,(j, B) →
    ∙ ▹ M ⊢s σ1 ≡ σ2 : Γ →
    _A = A <[ σ1] →
    _B = B<[var 0 .: σ1 >> ren_term S] →
    ∙ ,, (i, _A) ,, (j, _B) ▹ M ⊢s ((var 0) .: (var 1 .: (σ1 >> ren_term (S >> S)))) ≡ ((var 0) .: (var 1 .: (σ2 >> ren_term (S >> S)))) : (Γ ,, (i, A)) ,,(j, B).
Proof.
    intros. subst.
    dependent destruction H. dependent destruction H.
    eapply subst_ty in H2 as H2'. 3,4:eauto using validity_subst_conv_left. 2:econstructor.
    eapply subst_ty in H1 as H1'.
    3:eapply lift_subst in H0; eauto using validity_subst_conv_left, validity_ty_ctx.
    2,3:econstructor; eauto using ctx_typing.
    assert (forall σ, pointwise_relation _ eq (var 0 .: (var 1 .: σ >> ren_term (S >> S))) (up_term (up_term σ))).
    { intros. unfold pointwise_relation; intros; destruct a.
      1:reflexivity. 1:destruct a.  1:reflexivity. 1:ssimpl; reflexivity. }
    setoid_rewrite H3. eapply conv_substs_up_two; eauto.
    econstructor; eauto. econstructor; eauto using ctx_typing.
Qed.

Definition obseq_sym l A a b e : term :=
  J l A a (obseq l (S ⋅ A) (var 0) (S ⋅ a)) (obsrefl l A a) b e.

Lemma type_obseq_sym  M : forall Γ n A a b e,
    Γ ▹ M ⊢< prop > e : obseq (ty n) A a b →
    Γ ▹ M ⊢< prop > obseq_sym (ty n) A a b e : obseq (ty n) A b a.
Proof.
  intros. eapply validity_ty_ty in H as H'.
  eapply type_inv in H'. dependent destruction H'.
  unfold obseq_sym.
  eapply meta_conv.
  1:eapply type_J; eauto. all: rasimpl. 3:reflexivity.
  2:eapply type_obsrefl; eauto.
  eapply type_obseq.
  2:eapply meta_conv. 2: eapply type_var.
  2:eauto using validity_ty_ctx, ctx_cons.
  3:reflexivity.
  2:econstructor.
  all:eapply type_ren; eauto using ctx_typing, WellRen_S, validity_ty_ctx.
Qed.

Lemma conv_cast' M   :
  ∀ Γ i A A' B B' e e' a a',
    Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ▹ M ⊢< Ax i > B ≡ B' : Sort i ->
    Γ ▹ M ⊢< prop > e ≡ e' : obseq (Ax i) (Sort i) A B ->
    Γ ▹ M ⊢< i > a ≡ a' : A ->
    Γ ▹ M ⊢< i > cast i A B e a ≡ cast i A' B' e' a' : B.
Proof.
  intros. eapply conv_cast; eauto using validity_conv_left.
  eapply type_conv. 1:eauto using validity_conv_right. 
  econstructor;eauto using conversion, validity_ty_ctx, validity_conv_left.
Qed.

Lemma conv_cast_refl' M   Γ i A B e a :
  Γ ▹ M ⊢< Ax i > A ≡ B : Sort i ->
  Γ ▹ M ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
  Γ ▹ M ⊢< i > a : A ->
  Γ ▹ M ⊢< i > cast i A B e a ≡ a : B.
Proof.
  intros hAB he ha.
  eapply conv_trans.
  - econstructor.
    + eapply conv_refl_conv. eassumption.
    + apply conv_sym. eassumption.
    + eassumption.
    + eapply type_conv; eauto 7 using conversion, validity_ty_ctx, conv_refl.
    + apply conv_refl. assumption.
    + apply conv_refl. assumption.
  - econstructor. 2: eassumption.
    econstructor; eauto using validity_conv_left.
    econstructor. 1: eassumption.
    constructor.
    + constructor. eapply validity_ty_ctx. eassumption.
    + eapply conv_refl_conv. eassumption.
    + apply conv_sym. assumption.
Qed.

Lemma type_accinv' M  Γ n A R a p b r l T :
    Γ ▹ M ⊢< prop > p : acc (ty n) A R a →
    Γ ▹ M ⊢< ty n > b : A →
    Γ ▹ M ⊢< prop > r : R <[a.:b..] →
    T = acc (ty n) A R b →
    l = prop →
    Γ ▹ M ⊢< l > accinv (ty n) A R a p b r : T.
Proof.
  intros. subst. eapply validity_ty_ty in H as temp.
  eapply type_inv in temp. dependent destruction temp.
  eapply type_accinv; eauto.
Qed.


Lemma conv_accel' M   :
    ∀ Γ n l A A' R R' a a' q q' P P' p p' P0,
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax l > P ≡ P' : Sort l ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p ≡ p' : P'' ->
    Γ ▹ M ⊢< ty n > a ≡ a': A ->
    Γ ▹ M ⊢< prop > q ≡ q' : acc (ty n) A R a ->
    P0 = P <[a ..] ->
    Γ ▹ M ⊢< l > accel (ty n) l A R P p a q ≡ accel (ty n) l A' R' P' p' a' q' : P0.
Proof.
  intros. subst.
  eapply conv_accel; eauto 8 using validity_conv_left, typing, conversion.
Qed.

Lemma conv_accel_accin' M   :
    ∀ Γ n l A R a q P p,
    M = mdef ->
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p : P'' ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< prop > q : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) l Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam (ty n) l A t4 t3 in
    Γ ▹ M ⊢< l > accel (ty n) l A R P p a q ≡ p <[ t5 .: a ..] : P <[a ..].
Proof.
  intros. destruct l.
  - eapply conv_accel_accin; eauto.
  - eapply conv_irrel. 
    + eapply type_accel; eauto.
    + eapply subst_ty; eauto using validity_ty_ctx. 2:unfold P'';rasimpl;reflexivity.
      econstructor. 1:econstructor. all:ssimpl; eauto.
      1:eapply subst_id; eauto using validity_ty_ctx.
      eapply meta_conv. 1:eapply t5Wt; eauto.
      unfold B, R', P'. rasimpl. f_equal. f_equal. substify. ssimpl. reflexivity.
Qed.
    

