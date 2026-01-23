From Stdlib Require Import Arith.
Require Import library.
Require Import ZF_axioms ZF_library ZF_nat ZF_acc.
Require Import HO HO_pi HO_forall HO_box.

Definition ext := ctxExt.
Definition var0 := ctx_var0.
Definition wk := ctx_wk.

(* Accessibility predicate *)

Definition accTy_HO (n : nat) (A R a : ZFSet -> ZFSet) : ZFSet -> ZFSet :=
  fun γ => subsingl (acc (𝕌el n (A γ)) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (a γ)).

Lemma accTy_HO_typing {n : nat} {Γ : ZFSet} {A R a : ZFSet -> ZFSet}
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HR : ∀ γaa ∈ ext n (ext n Γ A) (fun γa => A (wk n Γ A γa)), R γaa ∈ Ω)
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ)) :
  ∀ γ ∈ Γ, accTy_HO n A R a γ ∈ Ω.
Proof.
  intros γ Hγ. unfold accTy_HO. apply subsingl_typing.
Qed.

(* Introduction rule for accessibility *)

Definition accinTm_HO (n : nat) (A R a : ZFSet -> ZFSet) : ZFSet -> ZFSet := fun _ => ∅.

Lemma accinTm_HO_typing {n : nat} {Γ : ZFSet} {A R a : ZFSet -> ZFSet}
  (A' := fun γa => A (wk n Γ A γa))
  (A'' := fun γaa => A' (wk n (ext n Γ A) A' γaa))
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (HR : ∀ γaa ∈ ext n (ext n Γ A) A', R γaa ∈ Ω) (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ))
  (Hq : ∀ γ ∈ Γ, ∅ ∈ forallTy_HO n A (implTy_HO (fun γa => R ⟨ ⟨ γ ; a (wk n Γ A γa) ⟩ ; var0 n Γ A γa ⟩)
                                                (accTy_HO n A' (fun γaaa => R ⟨ ⟨ wk n Γ A (wk n (ext n Γ A) A' (wk n (ext n (ext n Γ A) A') A'' γaaa)) ; var0 n (ext n Γ A) A' (wk n (ext n (ext n Γ A) A') A'' γaaa) ⟩ ; var0 n (ext n (ext n Γ A) A') A'' γaaa ⟩) (var0 n Γ A))) γ) :
  ∀ γ ∈ Γ, ∅ ∈ accTy_HO n A R a γ.
Proof.
  assert (∀ γa ∈ ext n Γ A, A' γa ∈ 𝕌 n) as HA'.
  { intros γa Hγa. apply HA. now apply ctx_wk_typing. }
  assert (∀ γaa ∈ ext n (ext n Γ A) A', A'' γaa ∈ 𝕌 n) as HA''.
  { intros γaa Hγaa. apply HA'. now apply ctx_wk_typing. }
  intros γ Hγ. apply subsingl_true_iff. apply acc_intro.
  - now apply Ha.
  - intros b Hb Hb2. specialize (Hq γ Hγ). apply subsingl_true_if in Hq. specialize (Hq b Hb).
    apply subsingl_true_if in Hq. assert (∅ ∈ R ⟨ ⟨ γ; a (wk n Γ A ⟨ γ; b ⟩) ⟩; var0 n Γ A ⟨ γ; b ⟩ ⟩).
    { clear Hq. refine (transp2S (fun X Y => ∅ ∈ R ⟨ ⟨ γ ; a X ⟩ ; Y ⟩) (sym _) (sym _) Hb2).
      now apply ctxExtβ1. now apply ctxExtβ2. }
    apply Hq in H. apply subsingl_true_if in H.
    assert (𝕌el n (A γ) ≡ 𝕌el n (A' ⟨ γ ; b ⟩)) as H1.
    { refine (fequal (fun X => 𝕌el n (A X)) (sym _)).  now apply ctxExtβ1. } destruct H1.
    assert (b ≡ var0 n Γ A ⟨ γ ; b ⟩) as H1.
    { refine (sym _). now apply ctxExtβ2. } destruct H1.
    refine (acc_cong (𝕌el n (A γ)) _ _ _ _ H). clear H. intros c Hc d Hd Hdc.
    assert (d ∈ 𝕌el n (A' ⟨ γ ; b ⟩)).
    { refine (transpS (fun X => d ∈ 𝕌el n (A X)) (sym _) Hd). now apply ctxExtβ1. }
    assert (c ∈ 𝕌el n (A'' ⟨ ⟨ γ; b ⟩; d ⟩)).
    { refine (transpS (fun X => c ∈ 𝕌el n (A X)) (sym _) Hc). refine (trans (fequal (wk n Γ A) _) _).
      apply ctxExtβ1 ; try assumption. now apply ctxExt_typing. now apply ctxExtβ1. }
    refine (transp2S (fun X Y => ∅ ∈ R ⟨ X ; Y ⟩) (fequal2 (fun X Y => ⟨ X ; Y ⟩) (sym _) (sym _)) (sym _) Hdc).
    + refine (trans (fequal (fun X => wk n Γ A (wk n (ext n Γ A) A' X)) _) _).
      { apply ctxExtβ1 ; try assumption. apply ctxExt_typing ; try assumption. now apply ctxExt_typing. }
      refine (trans (fequal (wk n Γ A) _) _).
      {  apply ctxExtβ1 ; try assumption. now apply ctxExt_typing. }
      now apply ctxExtβ1.
    + refine (trans (fequal (fun X => var0 n (ext n Γ A) A' X) _) _).
      { apply ctxExtβ1 ; try assumption. apply ctxExt_typing ; try assumption. now apply ctxExt_typing. }
      apply ctxExtβ2 ; try assumption. now apply ctxExt_typing.
    + apply ctxExtβ2 ; try assumption. apply ctxExt_typing ; try assumption. now apply ctxExt_typing.
Qed.

(* Eliminator of accessibility
   Here, we need some auxiliary functions to "adjust" the shape of the recursion hypothesis
   (i.e., to convert beween (Π (b : { x ∈ A | R x a}) . P b) and (Π (b : A) Π (_ : R b a) . P b)) *)

Definition adjust_aux (m : nat) (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (a f b : ZFSet) :=
  relToGraph (subsingl (R b a)) (𝕍 m) (HO_rel (fun _ => setAppArr { x ϵ A ∣ R x a } (𝕍 m) f b)).

Definition adjust (n m : nat) (A : ZFSet) (R : ZFSet -> ZFSet -> SProp) (a f : ZFSet) : ZFSet :=
  relToGraph A (𝕍 (max n m)) (HO_rel (fun b => adjust_aux m A R a f b)).

Definition accelimTm_HO (n m : nat) (A R P p a : ZFSet -> ZFSet) :=
  fun γ => accrec m (𝕌el n (A γ)) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) (fun x => 𝕌el m (P ⟨ γ ; x ⟩))
             (fun x f => p ⟨ ⟨ γ ; x ⟩ ; adjust n m (𝕌el n (A γ)) (fun x y => ∅ ∈ R ⟨ ⟨ γ ; y ⟩ ; x ⟩) x f ⟩) (a γ).

Lemma adjust_aux_typing {m : nat} {A f a b : ZFSet} {P : ZFSet -> ZFSet} {R : ZFSet -> ZFSet -> SProp}
  (HP : ∀ a ∈ A, P a ∈ 𝕍 m) (Ha : a ∈ A)
  (Hf : f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 m) (Hf2 : ∀ b ∈ A, R b a -> setAppArr { x ϵ A ∣ R x a } (𝕍 m) f b ∈ P b)
  (Hb : b ∈ A) :
  adjust_aux m A R a f b ∈ setPi m (subsingl (R b a)) (fun _ : ZFSet => P b).
Proof.
  apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing. intros x Hx. apply subsingl_true_if in Hx.
    apply setAppArr_typing. exact Hf. apply ZFincomp. now split.
  - intros x Hx. refine (transpS (fun X => X ∈ P b) (sym (setAppArr_HO _ Hx)) _).
    + clear x Hx. intros x Hx. apply subsingl_true_if in Hx. 
      apply (setAppArr_typing Hf). apply ZFincomp. now split.
    + apply Hf2. exact Hb. now apply subsingl_true_if in Hx.
Qed.

Lemma adjust_aux_sorting {n m : nat} {A f a b : ZFSet} {P : ZFSet -> ZFSet} {R : ZFSet -> ZFSet -> SProp}
  (HA : A ∈ 𝕍 n) (HP : ∀ a ∈ A, P a ∈ 𝕍 m) (Ha : a ∈ A)
  (Hf : f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 m) (Hf2 : ∀ b ∈ A, R b a -> setAppArr { x ϵ A ∣ R x a } (𝕍 m) f b ∈ P b)
  (Hb : b ∈ A) :
  adjust_aux m A R a f b ∈ 𝕍 (Nat.max n m).
Proof.
  eapply (ZFuniv_trans _ _ (setPi m (subsingl (R b a)) (fun _ => P b))).
  + now apply adjust_aux_typing.
  + eapply univ_le_incl. apply Nat.le_max_r. apply setPi_typing.
    * eapply ZFuniv_trans. apply subsingl_typing. apply Ω_typing.
    * intros x Hx. now apply HP.
Qed.

Lemma adjust_typing {n m : nat} {A f a : ZFSet} {P : ZFSet -> ZFSet} {R : ZFSet -> ZFSet -> SProp}
  (HA : A ∈ 𝕍 n) (HP : ∀ a ∈ A, P a ∈ 𝕍 m) (Ha : a ∈ A)
  (Hf : f ∈ { b ϵ A ∣ R b a } ⇒ 𝕍 m) (Hf2 : ∀ b ∈ A, R b a -> setAppArr { x ϵ A ∣ R x a } (𝕍 m) f b ∈ P b) :
  adjust n m A R a f ∈ setPi (Nat.max n m) A (fun b => setPi m (subsingl (R b a)) (fun _ => P b)).
Proof.
  apply ZFincomp. split.
  - apply relToGraph_typing. apply HO_rel_typing. intros b Hb. now apply (adjust_aux_sorting HA HP Ha Hf Hf2 Hb).
  - intros b Hb. refine (transpS (fun X => X ∈ _) (sym (setAppArr_HO _ Hb)) _).
    clear b Hb. intros b Hb.
    + now apply (adjust_aux_sorting HA HP Ha Hf Hf2 Hb).
    + now apply adjust_aux_typing. 
Qed.

Lemma subsingl_eta {P : ZFSet} (HP : P ∈ Ω) : subsingl (∅ ∈ P) ≡ P.
Proof.
  apply ZFext.
  - intros x Hx. destruct (sym (proof_irr (subsingl_typing _) _ Hx)). now apply subsingl_true_if in Hx.
  - intros x Hx. destruct (sym (proof_irr HP _ Hx)). now apply subsingl_true_iff.
Qed.

Lemma adjust_HO_typing {n m : nat} {Γ γ f a : ZFSet} {A R P p : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (A' := fun γa => A (wk n Γ A γa))
  (HR : ∀ γaa ∈ ext n (ext n Γ A) A', R γaa ∈ Ω) (HP : ∀ γa ∈ ext n Γ A, P γa ∈ 𝕌 m)
  (R' := fun γaa => R γaa)
  (P' := fun γaah => P ⟨ wk n Γ A (wk n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah))
                       ; var0 n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah) ⟩)
  (B := fun γa => piTy_HO n m A' (piTy_HO 0 m (boxTy_HO R') P') γa)
  (Hp : ∀ γax ∈ ext (max n m) (ext n Γ A) B, p γax ∈ 𝕌el m (P (wk (max n m) (ext n Γ A) B γax)))
  (Ha : a ∈ 𝕌el n (A γ)) (Ha2 : ∀ b ∈ 𝕌el n (A γ), ∅ ∈ R ⟨ ⟨ γ; a ⟩; b ⟩ -> acc (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) b) 
  (Hγ : γ ∈ Γ) (Hf : f ∈ {b ϵ 𝕌el n (A γ) ∣ ∅ ∈ R ⟨ ⟨ γ; a ⟩; b ⟩} ⇒ 𝕍 m)
  (Hf2 : ∀ b ∈ 𝕌el n (A γ), ∅ ∈ R ⟨ ⟨ γ; a ⟩; b ⟩ -> setAppArr {b ϵ 𝕌el n (A γ) ∣ ∅ ∈ R ⟨ ⟨ γ; a ⟩; b ⟩} (𝕍 m) f b ∈ 𝕌el m (P ⟨ γ; b ⟩)) :
  adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ∈ 𝕌el (Nat.max n m) (B ⟨ γ; a ⟩).
Proof.
  (* Typing auxiliary definitions *)
  assert (Nat.max 0 m ≡ m) as Hmax.
  { rewrite (PeanoNat.Nat.max_0_l m). reflexivity. }
  assert (∀ γa ∈ ext n Γ A, A' γa ∈ 𝕌 n) as HA'.
  { intros γa Hγa. unfold A'. apply HA. now apply ctx_wk_typing. }
  assert (∀ γaa ∈ ext n (ext n Γ A) A', boxTy_HO R' γaa ∈ 𝕌 0) as HR'.
  { apply boxTy_HO_typing. exact HR. }
  assert (∀ γaah ∈ ext 0 (ext n (ext n Γ A) A') (boxTy_HO R), P' γaah ∈ 𝕌 m) as HP'.
  { intros γaah Hγaah. unfold P'. apply HP. apply (ctxExt_typing HA).
    - apply ctx_wk_typing. exact HA. apply ctx_wk_typing. exact HA'. now apply ctx_wk_typing.
    - apply (ctx_var0_typing HA'). now apply ctx_wk_typing. }
  assert (∀ γaa ∈ (ext n (ext n Γ A) A'), piTy_HO 0 m (boxTy_HO R') P' γaa ∈ 𝕌 m) as HPi.
  { refine (transpS (fun X => ∀ x ∈ ext n (ext n Γ A) A', piTy_HO 0 m (boxTy_HO R') P' x ∈ 𝕌 X) Hmax _).
    apply piTy_HO_typing. exact HR'. exact HP'. }
  assert (∀ γa ∈ ext n Γ A, B γa ∈ 𝕌 (max n m)) as HB.
  { unfold B. now apply piTy_HO_typing. }
  assert (⟨ γ ; a ⟩ ∈ ext n Γ A) as Hγa.
  { now apply ctxExt_typing. }
  (* Proving the goal *)
  unfold B. refine (transpS (fun X => _ ∈ X) (sym (el_piTy HA' HPi Hγa)) _).
  refine (transpS (fun X => adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ∈ X) _
            (adjust_typing (P := fun b => 𝕌el m (P ⟨ γ ; b ⟩)) _ _ Ha Hf Hf2)).
  - refine (trans (sym _) (fequal (fun X => setPi (max n m) (𝕌el n (A X)) _) (sym (ctxExtβ1 HA Hγ Ha)))).
    apply setPi_cong. intros b Hb.
    assert (b ∈ 𝕌el n (A' ⟨ γ; a ⟩)) as Hb2.
    { exact (transpS (fun X => b ∈ 𝕌el n (A X)) (sym (ctxExtβ1 HA Hγ Ha)) Hb). }
    assert (⟨ ⟨ γ; a ⟩; b ⟩ ∈ ext n (ext n Γ A) A') as Hγaa.
    { apply (ctxExt_typing HA' Hγa Hb2). }
    refine (transpS (fun X => 𝕌el X _ ≡ setPi X _ _) Hmax _).
    refine (trans (el_piTy (Γ := ext n (ext n Γ A) A') HR' HP' Hγaa) _).
    refine (trans _ (fequal (fun X => setPi _ X _) (trans (el_boxTy (n := 0) HR _ Hγaa) (sym (subsingl_eta (HR _ Hγaa)))))).
    apply setPi_cong. intros x Hx. refine (fequal2 (fun X Y => 𝕌el m (P ⟨ X ; Y ⟩)) _ _).
    + refine (trans (fequal (fun X => wk n Γ A (wk n _ A' X)) (ctxExtβ1 HR' Hγaa Hx)) _).
      refine (trans (fequal (fun X => wk n Γ A X) (ctxExtβ1 HA' Hγa Hb2)) _). 
      now apply ctxExtβ1.
    + refine (trans (fequal (fun X => var0 n (ext n Γ A) A' X) (ctxExtβ1 HR' Hγaa Hx)) _).
      now apply ctxExtβ2.
  - apply 𝕌el_typing. now apply HA.
  - intros c Hc. apply 𝕌el_typing. apply HP. now apply ctxExt_typing.
Qed.

(* Typing rule for the eliminator of accessibility *)
Lemma accelimTm_HO_typing {n m : nat} {Γ : ZFSet} {A R P p a : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (A' := fun γa => A (wk n Γ A γa))
  (HR : ∀ γaa ∈ ext n (ext n Γ A) A', R γaa ∈ Ω) (HP : ∀ γa ∈ ext n Γ A, P γa ∈ 𝕌 m)
  (R' := fun γaa => R γaa)
  (P' := fun γaah => P ⟨ wk n Γ A (wk n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah))
                       ; var0 n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah) ⟩)
  (B := fun γa => piTy_HO n m A' (piTy_HO 0 m (boxTy_HO R') P') γa)
  (Hp : ∀ γax ∈ ext (max n m) (ext n Γ A) B, p γax ∈ 𝕌el m (P (wk (max n m) (ext n Γ A) B γax)))
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ)) (Hq : ∀ γ ∈ Γ, ∅ ∈ accTy_HO n A R a γ) :
  ∀ γ ∈ Γ, accelimTm_HO n m A R P p a γ ∈ 𝕌el m (P ⟨ γ ; a γ ⟩).
Proof.
  (* Typing auxiliary definitions *)
  assert (Nat.max 0 m ≡ m) as Hmax.
  { rewrite (PeanoNat.Nat.max_0_l m). reflexivity. }
  assert (∀ γa ∈ ext n Γ A, A' γa ∈ 𝕌 n) as HA'.
  { intros γa Hγa. unfold A'. apply HA. now apply ctx_wk_typing. }
  assert (∀ γaa ∈ ext n (ext n Γ A) A', boxTy_HO R' γaa ∈ 𝕌 0) as HR'.
  { apply boxTy_HO_typing. exact HR. }
  assert (∀ γaah ∈ ext 0 (ext n (ext n Γ A) A') (boxTy_HO R), P' γaah ∈ 𝕌 m) as HP'.
  { intros γaah Hγaah. unfold P'. apply HP. apply (ctxExt_typing HA).
    - apply ctx_wk_typing. exact HA. apply ctx_wk_typing. exact HA'. now apply ctx_wk_typing.
    - apply (ctx_var0_typing HA'). now apply ctx_wk_typing. }
  assert (∀ γaa ∈ (ext n (ext n Γ A) A'), piTy_HO 0 m (boxTy_HO R') P' γaa ∈ 𝕌 m) as HPi.
  { refine (transpS (fun X => ∀ x ∈ ext n (ext n Γ A) A', piTy_HO 0 m (boxTy_HO R') P' x ∈ 𝕌 X) Hmax _).
    apply piTy_HO_typing. exact HR'. exact HP'. }
  assert (∀ γa ∈ ext n Γ A, B γa ∈ 𝕌 (max n m)) as HB.
  { unfold B. now apply piTy_HO_typing. }
  (* Proving the goal *)
  intros γ Hγ. cbn. unfold accelimTm_HO. 
  assert (acc (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (a γ)) as Hq'.
  { specialize (Hq γ Hγ). cbn in Hq. apply subsingl_true_if in Hq. exact Hq. }
  refine (accrec_typing (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (P := fun x => 𝕌el m (P ⟨ γ; x ⟩)) _ _ (Ha γ Hγ) Hq').
  - clear a Ha Hq Hq'. intros a Ha. apply 𝕌el_typing. apply HP. now apply ctxExt_typing. 
  - clear a Ha Hq Hq'. intros a Ha f Hf Ha2 Hf2.
    assert (⟨ γ ; a ⟩ ∈ ext n Γ A) as Hγa.
    { now apply ctxExt_typing. }
    assert (adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ∈ 𝕌el (Nat.max n m) (B ⟨ γ; a ⟩)) as Hf3.
    { apply (adjust_HO_typing HA HR HP Hp Ha Ha2 Hγ Hf Hf2). }
    assert (wk (Nat.max n m) (ext n Γ A) B ⟨ ⟨ γ; a ⟩
                                           ; adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ⟩ ≡ ⟨ γ; a ⟩) as H.
    { apply (ctxExtβ1 HB). now apply ctxExt_typing. apply Hf3. }
    refine (transpS (fun X => _ ∈ 𝕌el m (P X)) H _). apply Hp.
    apply (ctxExt_typing HB). now apply ctxExt_typing. exact Hf3.
Qed.

(* Computation rule for accessibility. Difficult to read because of all the massaging, but the
   point is that (accelimTm_HO n m A R P p a γ) unfolds to p applied to the recursive call *)
Lemma accelimTm_HO_β {n m : nat} {Γ : ZFSet} {A R P p a : ZFSet -> ZFSet} 
  (HA : ∀ γ ∈ Γ, A γ ∈ 𝕌 n) (A' := fun γa => A (wk n Γ A γa))
  (HR : ∀ γaa ∈ ext n (ext n Γ A) A', R γaa ∈ Ω) (HP : ∀ γa ∈ ext n Γ A, P γa ∈ 𝕌 m)
  (P' := fun γaah => P ⟨ wk n Γ A (wk n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah))
                       ; var0 n (ext n Γ A) A' (wk 0 (ext n (ext n Γ A) A') (boxTy_HO R) γaah) ⟩)
  (B := fun γa => piTy_HO n m A' (piTy_HO 0 m (boxTy_HO R) P') γa)
  (Hp : ∀ γax ∈ ext (max n m) (ext n Γ A) B, p γax ∈ 𝕌el m (P (wk (max n m) (ext n Γ A) B γax)))
  (Ha : ∀ γ ∈ Γ, a γ ∈ 𝕌el n (A γ)) (Hq : ∀ γ ∈ Γ, ∅ ∈ accTy_HO n A R a γ) :
  ∀ γ ∈ Γ, accelimTm_HO n m A R P p a γ ≡ p ⟨ ⟨ γ ; a γ ⟩ ; adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (a γ)
                                                              (relToGraph {b ϵ 𝕌el n (A γ) ∣ ∅ ∈ R ⟨ ⟨ γ; a γ ⟩; b ⟩} (𝕍 m)
                                                                 (HO_rel
                                                                    (fun b : ZFSet =>
                                                                       accrec m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (fun x : ZFSet => 𝕌el m (P ⟨ γ; x ⟩))
                                                                         (fun x f : ZFSet => p ⟨ ⟨ γ; x ⟩; adjust n m (𝕌el n (A γ)) (fun x0 y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x0 ⟩) x f ⟩) b))) ⟩.
Proof.
  (* Typing auxiliary definitions *)
  assert (Nat.max 0 m ≡ m) as Hmax.
  { rewrite (PeanoNat.Nat.max_0_l m). reflexivity. }
  assert (∀ γa ∈ ext n Γ A, A' γa ∈ 𝕌 n) as HA'.
  { intros γa Hγa. unfold A'. apply HA. now apply ctx_wk_typing. }
  assert (∀ γaa ∈ ext n (ext n Γ A) A', boxTy_HO R γaa ∈ 𝕌 0) as HR'.
  { apply boxTy_HO_typing. exact HR. }
  assert (∀ γaah ∈ ext 0 (ext n (ext n Γ A) A') (boxTy_HO R), P' γaah ∈ 𝕌 m) as HP'.
  { intros γaah Hγaah. unfold P'. apply HP. apply (ctxExt_typing HA).
    - apply ctx_wk_typing. exact HA. apply ctx_wk_typing. exact HA'. now apply ctx_wk_typing.
    - apply (ctx_var0_typing HA'). now apply ctx_wk_typing. }
  assert (∀ γaa ∈ (ext n (ext n Γ A) A'), piTy_HO 0 m (boxTy_HO R) P' γaa ∈ 𝕌 m) as HPi.
  { refine (transpS (fun X => ∀ x ∈ ext n (ext n Γ A) A', piTy_HO 0 m (boxTy_HO R) P' x ∈ 𝕌 X) Hmax _).
    apply piTy_HO_typing. exact HR'. exact HP'. }
  assert (∀ γa ∈ ext n Γ A, B γa ∈ 𝕌 (max n m)) as HB.
  { unfold B. now apply piTy_HO_typing. }
  (* Proving the goal *)
  intros γ Hγ.
  assert (acc (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (a γ)) as Hq'.
  { specialize (Hq γ Hγ). cbn in Hq. apply subsingl_true_if in Hq. exact Hq. }
  cbn. unfold accelimTm_HO. refine (trans _ _).
  - refine (accrec_β (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) (P := fun x => 𝕌el m (P ⟨ γ; x ⟩)) _ _ (Ha γ Hγ) Hq').
    + clear a Ha Hq Hq'.
      intros a Ha. apply 𝕌el_typing. apply HP. now apply ctxExt_typing. 
    + clear a Ha Hq Hq'.
      intros a Ha f Hf Ha2 Hf2. assert (⟨ γ ; a ⟩ ∈ ext n Γ A) as Hγa.
      { now apply ctxExt_typing. }
      assert (adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ∈ 𝕌el (Nat.max n m) (B ⟨ γ; a ⟩)) as Hf3.
      { apply (adjust_HO_typing HA HR HP Hp Ha Ha2 Hγ Hf Hf2). }
      assert (wk (Nat.max n m) (ext n Γ A) B ⟨ ⟨ γ; a ⟩
                                               ; adjust n m (𝕌el n (A γ)) (fun x y : ZFSet => ∅ ∈ R ⟨ ⟨ γ; y ⟩; x ⟩) a f ⟩ ≡ ⟨ γ; a ⟩) as H.
      { apply (ctxExtβ1 HB). now apply ctxExt_typing. apply Hf3. }
      refine (transpS (fun X => _ ∈ 𝕌el m (P X)) H _). apply Hp.
      apply (ctxExt_typing HB). now apply ctxExt_typing. exact Hf3.
  - reflexivity.
Qed.

