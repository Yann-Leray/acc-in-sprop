From Stdlib Require Import Utf8 List Arith Bool Lia.
From AccInSProp Require Import
core unscoped AST SubstNotations RAsimpl AST_rasimpl
Util BasicAST Typing BasicMetaTheory Fundamental CHeqProps.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Import ListNotations.
Import CombineNotations.

Open Scope subst_scope. 
Reserved Notation " t ⊏ t' " (at level 21).

Inductive decoration : term → term → Prop :=
| dec_var x :
    var x ⊏ var x 

| dec_sort l :
    Sort l ⊏ Sort l 

| dec_assm c :
    assm c ⊏ assm c 

| dec_Pi i j A A' B B' :
    A ⊏ A' →
    B ⊏ B' →
    Pi i j A B ⊏ Pi i j A' B'

| dec_lam i j A A' B B' t t' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    lam i j A B t ⊏ lam i j A' B' t'

| dec_app i j A A' B B' t t' u u' :
    A ⊏ A' →
    B ⊏ B' →
    t ⊏ t' →
    u ⊏ u' →
    app i j A B t u ⊏ app i j A' B' t' u'

| dec_nat : 
    Nat ⊏ Nat 

| dec_zero :
    zero ⊏ zero

| dec_succ t t' :
    t ⊏ t' →
    succ t ⊏ succ t'

| dec_rec l P P' pz pz' ps ps' t t' :
    P ⊏ P' →
    pz ⊏ pz' →
    ps ⊏ ps' →
    t ⊏ t' →
    rec l P pz ps t ⊏ rec l P' pz' ps' t'

| dec_acc i A A' R R' a a' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    acc i A R a ⊏ acc i A' R' a'

| dec_accin i A A' R R' a a' p p' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    accin i A R a p ⊏ accin i A' R' a' p'

| dec_accinv i A A' R R' a a' p p' b b' r r' :
    A ⊏ A' →
    R ⊏ R' →
    a ⊏ a' →
    p ⊏ p' →
    b ⊏ b' →
    r ⊏ r' →
    accinv i A R a p b r ⊏ accinv i A' R' a' p' b' r'

| dec_accel i l A A' R R' P P' p p' a a' q q' :
    A ⊏ A' →
    R ⊏ R' →
    P ⊏ P' →
    p ⊏ p' →
    a ⊏ a' →
    q ⊏ q' →
    accel i l A R P p a q ⊏ accel i l A' R' P' p' a' q'

| dec_accelcomp i l A A' R R' P P' p p' a a' q q' :
    A ⊏ A' →
    R ⊏ R' →
    P ⊏ P' →
    p ⊏ p' →
    a ⊏ a' →
    q ⊏ q' →
    accelcomp i l A R P p a q ⊏ accelcomp i l A' R' P' p' a' q'

| dec_obseq i A A' a a' b b' :
    A ⊏ A' →
    a ⊏ a' →
    b ⊏ b' →
    obseq i A a b ⊏ obseq i A' a' b'

| dec_obsrefl i A A' a a' :
    A ⊏ A' →
    a ⊏ a' →
    obsrefl i A a ⊏ obsrefl i A' a'

| dec_J i A A' a a' P P' p p' b b' e e' :
    A ⊏ A' →
    a ⊏ a' →
    P ⊏ P' →
    p ⊏ p' →
    b ⊏ b' →
    e ⊏ e' →
    J i A a P p b e ⊏ J i A' a' P' p' b' e'

| dec_cast i A A' B B' e e' a a' :
    A ⊏ A' →
    B ⊏ B' →
    e ⊏ e' →
    a ⊏ a' →
    cast i A B e a ⊏ cast i A' B' e' a'

| dec_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    injpi1 i j A1 A2 B1 B2 e ⊏ injpi1 i j A1' A2' B1' B2' e'

| dec_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ⊏ A1' →
    A2 ⊏ A2' →
    B1 ⊏ B1' →
    B2 ⊏ B2' →
    e ⊏ e' →
    a2 ⊏ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ⊏ injpi2 i j A1' A2' B1' B2' e' a2'

| add_cast i A B e a b :
    a ⊏ b →
    a ⊏ cast i A B e b

where "u ⊏ v" := (decoration u v).


Definition ctx_dec (Γ Δ : ctx) :=
  Forall2 (λ u v, fst u = fst v ∧ snd u ⊏ snd v) Γ Δ.

Notation " Γ ⊂ Δ " := (ctx_dec Γ Δ) (at level 19).



Reserved Notation " t ~ t' " (at level 19).

Inductive simdec : term → term → Prop :=
| sim_var x :
    var x ~ var x 

| sim_sort l :
    Sort l ~ Sort l 

| sim_assm c :
    assm c ~ assm c 

| sim_Pi i j A A' B B' :
    A ~ A' →
    B ~ B' →
    Pi i j A B ~ Pi i j A' B'

| sim_lam i j A A' B B' t t' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    lam i j A B t ~ lam i j A' B' t'

| sim_app i j A A' B B' t t' u u' :
    A ~ A' →
    B ~ B' →
    t ~ t' →
    u ~ u' →
    app i j A B t u ~ app i j A' B' t' u'

| sim_nat : 
    Nat ~ Nat 

| sim_zero :
    zero ~ zero

| sim_succ t t' :
    t ~ t' →
    succ t ~ succ t'

| sim_rec l P P' pz pz' ps ps' t t' :
    P ~ P' →
    pz ~ pz' →
    ps ~ ps' →
    t ~ t' →
    rec l P pz ps t ~ rec l P' pz' ps' t'

| sim_acc i A A' R R' a a' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    acc i A R a ~ acc i A' R' a'

| sim_accin i A A' R R' a a' p p' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    accin i A R a p ~ accin i A' R' a' p'

| sim_accinv i A A' R R' a a' p p' b b' r r' :
    A ~ A' →
    R ~ R' →
    a ~ a' →
    p ~ p' →
    b ~ b' →
    r ~ r' →
    accinv i A R a p b r ~ accinv i A' R' a' p' b' r'

| sim_accel i l A A' R R' P P' p p' a a' q q' :
    A ~ A' →
    R ~ R' →
    P ~ P' →
    p ~ p' →
    a ~ a' →
    q ~ q' →
    accel i l A R P p a q ~ accel i l A' R' P' p' a' q'

| sim_accelcomp i l A A' R R' P P' p p' a a' q q' :
    A ~ A' →
    R ~ R' →
    P ~ P' →
    p ~ p' →
    a ~ a' →
    q ~ q' →
    accelcomp i l A R P p a q ~ accelcomp i l A' R' P' p' a' q'

| sim_obseq i A A' a a' b b' :
    A ~ A' →
    a ~ a' →
    b ~ b' →
    obseq i A a b ~ obseq i A' a' b'

| sim_obsrefl i A A' a a' :
    A ~ A' →
    a ~ a' →
    obsrefl i A a ~ obsrefl i A' a'

| sim_J i A A' a a' P P' p p' b b' e e' :
    A ~ A' →
    a ~ a' →
    P ~ P' →
    p ~ p' →
    b ~ b' →
    e ~ e' →
    J i A a P p b e ~ J i A' a' P' p' b' e'

| sim_injpi1 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    injpi1 i j A1 A2 B1 B2 e ~ injpi1 i j A1' A2' B1' B2' e'

| sim_injpi2 i j A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2' :
    A1 ~ A1' →
    A2 ~ A2' →
    B1 ~ B1' →
    B2 ~ B2' →
    e ~ e' →
    a2 ~ a2' →
    injpi2 i j A1 A2 B1 B2 e a2 ~ injpi2 i j A1' A2' B1' B2' e' a2'

| sim_castR i A B e a b :
    b ~ a →
    b ~ cast i A B e a

| sim_castL i A B e a b :
    a ~ b →
    cast i A B e a ~ b

where "u ~ v" := (simdec u v).


Lemma sim_cast i A A' B B' e e' a a' :
    a ~ a' →
    cast i A B e a ~ cast i A' B' e' a'.
Proof.
  intros. eauto using simdec.
Qed.


Lemma sim_refl t :
  t ~ t.
Proof.
  intros.
  induction t. 
  all: eauto using simdec.
Qed.

Lemma sim_sym u v :
  u ~ v -> v ~ u.
Proof.
  intros. induction H; eauto using simdec.
Qed.

Derive Signature for simdec.
Lemma sim_trans t u v :
  t ~ u -> u ~ v -> t ~ v.
Proof.
  intros. rename H0 into h. generalize v h. clear v h. induction H; intros.
  (* in some cases, dependent induction loops/takes a lot of time, so we do it by hand *)
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists w, w = app i j A' B' t' u' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists w, w = rec l P' pz' ps' t' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto 7 using simdec.
  - assert (exists w, w = accin i A' R' a' p' /\ w ~ v) as (w & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = accinv i A' R' a' p' b' r' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = accel i l A' R' P' p' a' q' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = accelcomp i l A' R' P' p' a' q' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - dependent induction h; eauto using simdec.
  - dependent induction h; eauto using simdec.
  - assert (exists t, t = J i A' a' P' p' b' e'  /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = injpi1 i j A1' A2' B1' B2' e' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - assert (exists t, t = injpi2 i j A1' A2' B1' B2' e' a2' /\ t ~ v) as (t & h1 & h2) by eauto.
    induction h2; dependent destruction h1.
    1:econstructor; eauto.
    eapply sim_castR. eauto.
  - apply IHsimdec. dependent induction h; eauto using simdec.
  - eapply IHsimdec in h. eauto using simdec.
Qed.

Lemma dec_refl u : 
  u ⊏ u.
Proof.
  intros.
  induction u. 
  all: eauto using decoration.
Qed.

Lemma dec_trans u v w :
  u ⊏ v →
  v ⊏ w →
  u ⊏ w.
Proof.
  intros. generalize w H0. clear w H0. induction H; intros w hw.
  1,2,3,4,5,7,8,9,11,16,17:dependent induction hw; eauto using decoration.
  - assert (exists s, s = app i j A' B' t' u' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = rec l P' pz' ps' t' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = accin i A' R' a' p' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto.
  - assert (exists s, s = accinv i A' R' a' p' b' r' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = accel i l A' R' P' p' a' q' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = accelcomp i l A' R' P' p' a' q' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = J i A' a' P' p' b' e' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = cast i A' B' e' a' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = injpi1 i j A1' A2' B1' B2' e' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - assert (exists s, s = injpi2 i j A1' A2' B1' B2' e' a2' /\ s ⊏ w) as (s & h1 & h2) by eauto.
    induction h2; dependent destruction h1; econstructor; eauto. 
  - dependent induction hw; econstructor; eauto.
Qed.


Lemma dec_to_sim u v :
  u ⊏ v →
  u ~ v.
Proof.
  intros. induction H; eauto using simdec.
Qed.

Lemma rename_dec ρ u v :
  u ⊏ v →
  ρ ⋅ u ⊏ ρ ⋅ v.
Proof.
  induction 1 in ρ |- *.
  all: solve [ cbn ; econstructor ; eauto ].
Qed.


Lemma subst_dec σ u v :
  u ⊏ v →
  u <[ σ ] ⊏ v <[ σ ].
Proof.
  intros. generalize σ. clear σ.
  induction H.
  all: try solve [ cbn ; econstructor ; eauto ].
  intros. eapply dec_refl.
Qed.

Definition dec_subst (σ θ : nat → term) :=
  ∀ x, σ x ⊏ θ x.

Lemma dec_subst_up σ θ :
  dec_subst σ θ →
  dec_subst (up_term σ) (up_term θ).
Proof.
  intros h [].
  - cbn. constructor.
  - cbn. unfold ">>". apply rename_dec. apply h.
Qed.

Lemma dec_subst_one u v :
  u ⊏ v →
  dec_subst (u..) (v..).
Proof.
  intros h [].
  - cbn. assumption.
  - cbn. constructor.
Qed.

Lemma dec_subst_scons u v σ σ' :
  u ⊏ v →
  dec_subst σ σ' →
  dec_subst (u .: σ) (v .: σ').
Proof.
  intros hu hs [].
  - cbn. assumption.
  - cbn. apply hs.
Qed.

Lemma dec_subst_refl σ :
  dec_subst σ σ.
Proof.
  intros. intro. apply dec_refl. 
Qed.

Lemma substs_dec σ θ u :
  dec_subst σ θ →
  u <[ σ ] ⊏ u <[ θ ].
Proof.
  intros. generalize σ θ H. clear σ θ H. induction u.
  all: try solve [ cbn ; econstructor ; eauto using dec_subst_up ].
  intros. eapply H.
Qed.

Lemma substs_decs σ θ u v :
  dec_subst σ θ →
  u ⊏ v →
  u <[ σ ] ⊏ v <[ θ ].
Proof.
  intros. generalize σ θ H. clear σ θ H.
  induction H0.
  all: try solve [ cbn ; econstructor ; eauto using decoration, dec_subst_up ].
  intros. eapply H.
Qed.

Lemma substs_decs_one u v a b :
  u ⊏ v →
  a ⊏ b →
  u <[ a .. ] ⊏ v <[ b .. ].
Proof.
  intros h1 h2.
  apply substs_decs. 2: auto.
  apply dec_subst_one. assumption.
Qed.

Lemma substs_decs_two u v a b c d :
  u ⊏ v →
  a ⊏ b →
  c ⊏ d →
  u <[ a .: c .. ] ⊏ v <[ b .: d .. ].
Proof.
  intros.
  apply substs_decs. 2: auto.
  eauto using dec_subst_scons, dec_subst_one.
Qed.

(* Fundamental lemma *)

Definition renX m := 3 * m.
Definition renR m := 1 + (3 * m).
Definition renL m := 2 + (3 * m).

(* invariant: the contexts are compatible *)
Fixpoint pack (Γ1 Γ2 : ctx) := 
  match Γ1, Γ2 with 
  | cons (l, A1) Γ1, cons (l', A2) Γ2 => (* invariant: l = l' *)
    let A1' := renL ⋅ A1 in
    let A2' := renR ⋅ A2 in
    let Aeq := heq l ((S >> S) ⋅ A1') ((S >> S) ⋅ A2') (var 1) (var 0) in
    pack Γ1 Γ2 ,, (l, A1') ,, (l, S ⋅ A2') ,, (prop, Aeq)
  | _,_ =>  ∙
  end.

Inductive ctx_compat : ctx -> ctx -> Prop := 
| compat_nil : ctx_compat ∙ ∙
| compat_cons Γ1 l1 A1 Γ2 l2 A2 : 
  l1 = l2 ->
  ctx_compat Γ1 Γ2 ->
  ctx_compat (Γ1 ,, (l1, A1)) (Γ2 ,, (l2, A2)).

Lemma WellRen_renL Γ1 Γ2 (h : ctx_compat Γ1 Γ2):
  pack Γ1 Γ2 ⊢r renL : Γ1.
Proof.
  induction h.
  - econstructor.
  - subst. unfold renL. econstructor.
    * simpl. eapply WellRen_weak,WellRen_weak,WellRen_weak. fold plus.
      eapply autosubst_simpl_WellRen. 2:eauto.
      econstructor. unfold pointwise_relation. intros.
      induction a; eauto.
      unfold renL in *.  simpl in *. rewrite IHa. lia.
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor. 1:econstructor.
      unfold renL; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma WellRen_renR Γ1 Γ2 (h : ctx_compat Γ1 Γ2):
  pack Γ1 Γ2 ⊢r renR : Γ2.
Proof.
  induction h.
  - econstructor.
  - subst. unfold renR. econstructor. 
    * simpl. eapply WellRen_weak,WellRen_weak. fold plus. 
      eapply autosubst_simpl_WellRen.
      2:eapply WellRen_weak. 2:eapply IHh. unfold renR. simpl.
      econstructor. unfold pointwise_relation. intros.
      unfold ">>". lia. 
    * eapply varty_meta. 1:cbn. 1:econstructor. 1:econstructor.
      unfold renR; ssimpl. eapply ren_term_morphism. 2:reflexivity.
      unfold pointwise_relation. intros. induction a.
      all:unfold ">>" in *; simpl in *; lia.
Qed.


Lemma pack_Wt Γ1 Γ2 :
  ctx_compat Γ1 Γ2 ->
  ⊢p Γ1 -> 
  ⊢p Γ2 -> 
  ⊢p pack Γ1 Γ2.
Proof.
  intro h. induction h.
  1:econstructor. subst.
  intros. dependent destruction H. dependent destruction H0.
  assert (pack Γ1 Γ2 ⊢p< Ax l2 > renL ⋅ A1 : Sort l2) by eauto using type_ren, WellRen_renL.
  assert (pack Γ1 Γ2,, (l2, renL ⋅ A1) ⊢p< Ax l2 > S ⋅ renR ⋅ A2 : Sort l2) 
    by (rasimpl; eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_renR). 
  simpl. econstructor. 1:econstructor. 1:econstructor.
  1:eauto.
  3:unfold Ax;simpl;eapply type_heq.
  1,2:assumption.
  * eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_S.
  * rasimpl. rasimpl in H4. eapply type_ren; eauto using ctx_typing, WellRen_weak, WellRen_renR.
  * econstructor; eauto using ctx_typing. eapply varty_meta. 1:econstructor. 1:econstructor.
    rasimpl. reflexivity.
  * econstructor; eauto using ctx_typing. eapply varty_meta. 1:econstructor.
    rasimpl. reflexivity.
Qed.


Lemma sim_var_heq l x A1 A2 Γ1 Γ2 :
  ⊢p Γ1 -> ⊢p Γ2 ->
  ctx_compat Γ1 Γ2 ->
  Γ1 ∋< l > x : A1 ->
  Γ2 ∋< l > x : A2 ->
  ∃ e, pack Γ1 Γ2 ⊢p< prop > e : heq l (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ (var x)) (renR ⋅ (var x)).
Proof.
  intros. generalize l x A1 A2 H H0 H2 H3. clear l x A1 A2 H H0 H2 H3. induction H1; intros.
  1:dependent destruction H2.
  subst.
  destruct x.
  - dependent destruction H3. dependent destruction H4.
    simpl. exists (var 0). econstructor.
    1:unshelve eapply (pack_Wt _ _ _ H0 H2); eauto using ctx_compat. 
    eapply varty_meta. 1:econstructor. ssimpl. rewrite heq_ren. unfold renL, renR. ssimpl. f_equal.
    all:eapply ren_term_morphism; eauto.
    all:unfold pointwise_relation; intros; unfold ">>"; lia.
  - dependent destruction H3. dependent destruction H4.
    dependent destruction H0. dependent destruction H2.  
    edestruct (IHctx_compat); eauto.
    eexists. eapply type_ren; eauto.
    1:eapply pack_Wt; eauto using ctx_typing, ctx_compat.
    1:simpl; eauto using WellRen_weak, WellRen_S.
    rewrite heq_ren. unfold renR, renL. rasimpl. unfold ">>". f_equal.
    3,4:eapply f_equal; lia.
    1,2:eapply ren_term_morphism; eauto.
    all:unfold pointwise_relation; intros; unfold ">>"; lia.
Qed.

Lemma sim_heq_ih_aux {u u'}: 
(forall (i : nat) (Γ1 Γ2 : ctx) (A1 A2 : term),
    ctx_compat Γ1 Γ2 → 
    Γ1 ⊢p< ty i > u : A1 → 
    Γ2 ⊢p< ty i > u' : A2 → 
    ∃ e : term, pack Γ1 Γ2 ⊢p< prop > e : heq (ty i) (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ u) (renR ⋅ u')) ->
(forall (l : level) (Γ1 Γ2 : ctx) (A1 A2 : term),
    ctx_compat Γ1 Γ2 → 
    Γ1 ⊢p< l > u : A1 → 
    Γ2 ⊢p< l > u' : A2 → 
    ∃ e : term, pack Γ1 Γ2 ⊢p< prop > e : heq l (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ u) (renR ⋅ u')).
Proof.
  intros. destruct l; eauto. eexists. eapply type_ren in H1, H2.
  3,6:eauto using WellRen_renL, WellRen_renR.
  3,5:reflexivity.
  2,3:eauto using validity_ty_ctx, pack_Wt. 
  eapply type_true_heq; eauto using validity_ty_ty.
Qed.
    

Lemma meta_ctx Γ l A Δ t :
  Γ ⊢p< l > t : A ->
  Γ = Δ ->
  Δ ⊢p< l > t : A.
Proof.
  intros. subst. assumption.
Qed.

Lemma sim_heq i Γ1 Γ2 t1 t2 A1 A2 :
  ctx_compat Γ1 Γ2 ->
  t1 ~ t2 →
  Γ1 ⊢p< ty i > t1 : A1 →
  Γ2 ⊢p< ty i > t2 : A2 →
  ∃ e, pack Γ1 Γ2 ⊢p< prop > e : heq (ty i) (renL ⋅ A1) (renR ⋅ A2) (renL ⋅ t1) (renR ⋅ t2).
Proof.
  intros hctx hsim h1 h2.
  induction hsim in i, Γ1, Γ2, hctx, A1, A2, h1, h2 |- *.
  all:try solve 
   [ eapply type_inv in h1; dependent destruction h1 ; dependent destruction lvl_eq ].
  all : assert (⊢p pack Γ1 Γ2) by eauto using pack_Wt, validity_ty_ctx.
  - pose proof h1 as h1'. pose proof h2 as h2'.
    eapply type_inv in h1. dependent destruction h1.
    eapply type_inv in h2. dependent destruction h2.
    eapply sim_var_heq in hctx as temp. 2-5:eauto using validity_ty_ctx, validity_conv_left.
    destruct temp.
    eexists. eapply type_conv. 1:eauto.
    eapply conv_heq.
    1,2:eapply conv_ren; eauto using conv_sym, WellRen_renL, WellRen_renR.
    all:eapply conv_refl, type_conv.
    1,3:eapply type_ren. 3:eapply WellRen_renL. 7:eapply WellRen_renR. 
    all: eauto.
    all:eapply conv_ren; eauto using WellRen_renL, WellRen_renR.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.  
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty. 3:eapply WellRen_renL. all:eauto.
    eapply conv_ren in conv_ty0. 3:eapply WellRen_renR. all:eauto.
    simpl in *.
    eexists. eapply type_conv.
    2:eapply conv_heq.
    1:eapply type_heq_refl.
    all:simpl.
    5,6:eapply conv_refl; econstructor; eauto.
    1,2:eapply meta_lvl. 1:eapply meta_conv.
    1,4:eauto using typing.
    1-3:reflexivity.
    all:eauto using conv_sym.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    
    edestruct IHhsim1. 2:eapply A_Wt. 2:eapply A_Wt0. 1:eauto.
    edestruct IHhsim2. 2:eapply B_Wt. 2:eapply B_Wt0. 1:eauto using ctx_compat.
    eexists. eapply type_conv.
    1:eapply type_heq_pi. 
    1,2:eapply type_ren. 1:eapply A_Wt. 4:eapply A_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR.
    1,2:eapply type_ren.
    1:eapply B_Wt. 4:eapply B_Wt0.
    1,4:eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1,3:eapply WellRen_up. 1,3:eauto using WellRen_renL,WellRen_renR.
    1-4:rasimpl;reflexivity.
    2:{ simpl in H1. unfold renR, renL in *. eapply meta_conv. 1:eapply H1. f_equal.
        all:ssimpl; substify; eapply subst_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>"; simpl.
        * destruct a; eauto. simpl. assert (forall x y, x = y -> var x = var y) by eauto. eapply H2. lia.
        * destruct a; eauto. 1:simpl. assert (forall x y, x = y -> var x = var y) by eauto. eapply H2. lia. }
    1:eauto.   
    eapply conv_heq.
    3,4:simpl; eapply conv_refl; eauto.
    3,4:eapply type_pi. 3-6:eapply type_ren; eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    3,4:eapply WellRen_up; eauto using WellRen_renL, WellRen_renR.
    1:change (Sort (Ru i0 j)) with (renL ⋅ (Sort (Ru i0 j))).
    2:change (Sort (Ru i0 j)) with (renR ⋅ (Sort (Ru i0 j))).
    1,2:eapply conv_ren; eauto using conv_sym, WellRen_renL, WellRen_renR.
    
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    unfold Ru in lvl_eq. destruct j; dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim1. 2:eapply A_Wt. 2:eapply A_Wt0. 1:eauto.
    edestruct IHhsim3. 2:eapply t_Wt. 2:eapply t_Wt0. 1:eauto using ctx_compat. 
    rasimpl in H0.
    eexists. eapply type_conv.
    1:eapply type_heq_lam. 3:eapply H0. 
    1,2:eapply type_ren. 1:eapply t_Wt. 4:eapply t_Wt0.
    2,5:eapply WellRen_up.
    1-8:eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    1:eapply meta_conv. 1:eapply H1.
    1:rasimpl;unfold renL, renR,">>";f_equal; eapply ren_term_morphism; eauto.
    1-4:unfold pointwise_relation; intros; destruct a; simpl; lia.
    eapply conv_heq.
    * change (Pi i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B)) with (renL ⋅ (Pi i0 (ty n) A B)).
      eapply conv_ren; eauto using WellRen_renL, conv_sym.
    * change (Pi i0 (ty n) (renR ⋅ A') (up_ren renR ⋅ B')) with (renR ⋅ (Pi i0 (ty n) A' B')).
      eapply conv_ren; eauto using WellRen_renR, conv_sym.
    * change (lam i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B) (up_ren renL ⋅ t)) with (renL ⋅ (lam i0 (ty n) A B t)).
      eapply conv_refl.
      1:eapply type_ren; eauto using WellRen_renL.
      1:eapply meta_lvl. 1:econstructor; eauto.
      all: eauto. 
    * change (lam i0 (ty n) (renL ⋅ A) (up_ren renL ⋅ B) (up_ren renL ⋅ t)) with (renL ⋅ (lam i0 (ty n) A B t)).
      eapply conv_refl.
      1:eapply type_ren; eauto using WellRen_renR.
      1:eapply meta_lvl. 1:econstructor; eauto.
      all: eauto.
  
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    unfold Ru in lvl_eq. destruct j; dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim3. 2:eapply t_Wt. 2:eapply t_Wt0. 1:eauto.
    pose proof (sim_heq_ih_aux IHhsim4) as IHhsim4'. 
    edestruct IHhsim4'. 2:eapply u_Wt. 2:eapply u_Wt0. 1:eauto using ctx_compat.
    rasimpl in H0. change (ty (ru i0 i)) with (Ru i0 (ty i)) in H0.
    eexists. eapply type_conv.
    1:eapply type_heq_app.
    5:eapply H0.
    5:eapply H1.
    1-4:eapply type_ren; eauto using WellRen_renL, WellRen_renR.
    eapply conv_heq; asimpl; renamify.
    1:replace (B <[ renL ⋅ u .: renL >> var]) with (renL ⋅ (B <[ u .: var])) by (rasimpl;reflexivity).
    1:eapply conv_ren; eauto using conv_sym, WellRen_renL.
    1:replace (B' <[ renR ⋅ u' .: renR >> var]) with (renR ⋅ (B' <[ u' .: var])) by (rasimpl;reflexivity).
    1:eapply conv_ren; eauto using conv_sym, WellRen_renR.
    1-2:eapply conv_refl. all:eapply meta_conv.
    1,3:eapply meta_lvl. 1,3:econstructor; eapply type_ren; eauto using WellRen_renL, ctx_typing, type_ren.
    1:eapply WellRen_up. all:eauto using WellRen_renL, WellRen_renR, ctx_typing, type_ren.
    2,3:rasimpl;reflexivity. eapply WellRen_up. all:eauto using WellRen_renR.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    eexists.
    eapply type_conv. 1:eapply type_heq_refl.
    3:eapply conv_heq.
    3,4 :eauto using conv_sym.
    3,4:eauto using conv_refl, typing.
    all:eapply meta_lvl;rasimpl;eauto using typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    eexists.
    eapply type_conv. 1:eapply type_heq_refl.
    3:eapply conv_heq.
    3,4 :eauto using conv_sym.
    3,4:eauto using conv_refl, typing.
    all:eapply meta_lvl;rasimpl;eauto using typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim; eauto. rasimpl in H0.
    eapply conv_ren in conv_ty, conv_ty0; eauto using WellRen_renL, WellRen_renR.
    rasimpl in conv_ty. rasimpl in conv_ty0.
    eexists. eapply type_conv.
    1:eapply type_heq_succ. 3:eapply H0. 1,2:eauto using type_ren, WellRen_renL, WellRen_renR.
    eapply conv_heq; eauto using conv_sym.
    all:eapply conv_refl, type_ren; eauto using WellRen_renL, WellRen_renR, typing.

  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    subst. clear lvl_eq0.

    edestruct IHhsim1. 2:exact P_Wt. 2:exact P_Wt0. 1:eauto using ctx_compat.
    edestruct IHhsim2; eauto.
    edestruct IHhsim3. 2:exact p_succ_Wt. 2:exact p_succ_Wt0.
    1:eauto using ctx_compat.
    edestruct IHhsim4; eauto.
    clear IHhsim1 IHhsim2 IHhsim3 IHhsim4.

    eexists. eapply type_conv.
    1:eapply type_heq_rec. 
    1,2:eapply type_ren. 1:exact P_Wt. 4:exact P_Wt0. 
    2,5:eapply WellRen_up. 1-8:eauto using ctx_typing, typing, WellRen_renL, WellRen_renR.
    1,4:eapply type_ren. 1:eapply p_zero_Wt. 4:eapply p_zero_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR. 1,2:rasimpl; reflexivity.
    1,3:eapply type_ren. 1:exact p_succ_Wt. 4:eapply p_succ_Wt0.
    2,5:eapply WellRen_up. 2,4:eapply WellRen_up; eauto using WellRen_renL, WellRen_renR.
    2,3,4,6:rasimpl;reflexivity.
    1,2:econstructor; eauto using ctx_typing, typing. 
    1,2:eapply type_ren; eauto using WellRen_up, WellRen_renL, WellRen_renR, typing, ctx_typing.
    1,2:eapply type_ren. 1:exact t_Wt. 4:exact t_Wt0. 1-6:eauto using WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply H0.
      unfold renL, renR; rasimpl. f_equal.
      all:eapply ren_term_morphism; eauto.
      all:unfold pointwise_relation; intros; unfold ">>"; simpl; destruct a; simpl; lia.
    * eapply meta_conv. 1:eapply H1.
      f_equal; rasimpl; eauto.
    * eapply meta_conv. 1:eapply meta_ctx.  1:eapply H2.
      ** simpl. unfold renL, renR. rasimpl. f_equal. 1:f_equal.
        1:f_equal. 1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal. 1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal. eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        3,4:eapply ren_term_morphism; eauto.
        3,4:unfold pointwise_relation; intros; unfold ">>"; destruct a; try destruct a; simpl; lia.
        1,2:eapply subst_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>"; destruct a; try destruct a; simpl; eauto.
        1,2:f_equal;lia.
    * eapply meta_conv. 1:eapply H3. 1:rasimpl; eauto.
    * eapply conv_heq. 
      1,3:replace ((up_ren renL ⋅ P) <[ (renL ⋅ t)..]) with (renL ⋅ (P <[t..])) by (rasimpl;reflexivity).
      3,4:replace ((up_ren renR ⋅ P') <[ (renR ⋅ t')..]) with (renR ⋅ (P' <[t'..])) by (rasimpl;reflexivity).
      2:replace (rec (ty i) (up_ren renL ⋅ P) (renL ⋅ pz) (up_ren (up_ren renL) ⋅ ps) (renL ⋅ t))
        with (renL ⋅ rec (ty i) P pz ps t) by (rasimpl;reflexivity).
      4:replace (rec (ty i) (up_ren renR ⋅ P') (renR ⋅ pz') (up_ren (up_ren renR) ⋅ ps') (renR ⋅ t'))
        with (renR ⋅ rec (ty i) P' pz' ps' t') by (rasimpl;reflexivity).
      all:eauto using conv_refl, conv_sym, type_ren, conv_ren, WellRen_renL, WellRen_renR, typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2. 
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim2. 2:exact B_Wt. 2:exact B_Wt0. 1:eauto using ctx_compat.
    edestruct IHhsim3; eauto.
    eexists. eapply type_conv.
    1:eapply type_heq_acc.
    1,3:eapply type_ren. 1:eapply B_Wt. 4:eapply B_Wt0.
    2,5:eapply WellRen_up. 2,4:eapply WellRen_up.
    1-10:eauto using WellRen_renL, WellRen_renR.
    2,3:rasimpl; reflexivity.
    1,2:econstructor; eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1,2:eapply type_ren. 1,5:eapply type_ren. 1,5:eauto. 8,11:eauto using WellRen_S.
    1-10:eauto using WellRen_renL, WellRen_renR, ctx_typing, type_ren.
    1,2:eapply type_ren. 1:eapply a_Wt. 4:eapply a_Wt0.
    1-6:eauto using WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply H0.
      ** simpl. unfold renL, renR. rasimpl.
        f_equal. 1:f_equal. 1:f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal.
        1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal.
        eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; try destruct a0; simpl; lia.
    * eapply H1.
    * eapply conv_heq.
      1,3:change (Sort prop) with (renL ⋅ (Sort prop)).
      3,4:change (Sort prop) with (renR ⋅ (Sort prop)).
      2,4:eapply conv_refl.
      all:eauto using type_ren, conv_ren, conv_sym, WellRen_renL, WellRen_renR, typing.
  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.

    clear hsim1 hsim2 hsim3 hsim4 hsim5 hsim6.
    clear IHhsim1.
    edestruct IHhsim2. 2:eapply R_Wt. 2:eapply R_Wt0. 1:eauto using ctx_compat. clear IHhsim2.
    edestruct IHhsim3. 2:eapply P_Wt. 2:eapply P_Wt0. 1:eauto using ctx_compat. clear IHhsim3.
    edestruct IHhsim4. 2:eapply p_Wt. 2:eapply p_Wt0. 1:eauto using ctx_compat. clear IHhsim4.
    edestruct IHhsim5; eauto using ctx_compat. clear IHhsim5 IHhsim6.

    eexists. eapply type_conv.
    1:eapply type_heq_accel.
    1,4:eapply type_ren. 1:eapply P_Wt. 4:eapply P_Wt0. 2,5:eapply WellRen_up.
    1-8:eauto using WellRen_renL, WellRen_renR.
    1,2:eauto using ctx_typing, WellRen_renL, WellRen_renR, type_ren.
    2,4:eapply type_ren. 2:eapply q_Wt. 5:eapply q_Wt0.
    2-7:eauto using WellRen_renL, WellRen_renR. 2,3:rasimpl; reflexivity.
    1,2:eapply type_ren. 1:eapply p_Wt. 4:eapply p_Wt0.
    2:eapply WellRen_up. 2:eapply WellRen_up. 2:eapply WellRen_renL.
    2,3: eauto using ctx_compat.
    2:unfold B, R'0, P'0; rasimpl; reflexivity.
    2:unfold P'';rasimpl;reflexivity.
    3:eapply WellRen_up. 3:eapply WellRen_up; eauto using WellRen_renR.
    3:unfold B0, R'1, P'1; rasimpl; reflexivity.
    3:unfold P''0;rasimpl;reflexivity.
    1,2:econstructor.
    1,3:eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    1:replace (Pi (ty n) (ty i) (S ⋅ renL ⋅ A) (Pi prop (ty i) ((1 .: (0 .: S >> S)) ⋅ (0 .: (1 .: renL >> (S >> S))) ⋅ R) ((1 .: (S >> S) >> S) ⋅ up_ren renL ⋅ P))) with ((up_ren renL) ⋅ B) by (unfold B, R'0, P'0; rasimpl; reflexivity).
    2:replace (Pi (ty n) (ty i) (S ⋅ renR ⋅ A') (Pi prop (ty i) ((1 .: (0 .: S >> S)) ⋅ (0 .: (1 .: renR >> (S >> S))) ⋅ R') ((1 .: (S >> S) >> S) ⋅ up_ren renR ⋅ P'))) with ((up_ren renR) ⋅ B0) by (unfold B0, R'1, P'1; rasimpl; reflexivity).
    1,2:eapply type_ren. 3, 7:eapply WellRen_up. 3,5:eauto using WellRen_renL, WellRen_renR. 3,4:eauto.
    1-6:eapply validity_ty_ctx in p_Wt; eapply validity_ty_ctx in p_Wt0; 
      dependent destruction p_Wt; dependent destruction p_Wt0; eauto using ctx_typing, type_ren, WellRen_renL, WellRen_renR.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply H0.
      ** simpl. unfold renL, renR. rasimpl.
        f_equal. 1:f_equal. 1:f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. 1:f_equal.
        1:eapply ren_term_morphism; eauto.
        1:unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
        f_equal. f_equal.
        eapply ren_term_morphism; eauto.
        unfold pointwise_relation; intros; unfold ">>"; destruct a; simpl; lia.
      ** simpl. unfold renL, renR. rasimpl. f_equal.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; try destruct a0; simpl; lia.
    * eauto.
    * eapply meta_conv. 1:eapply H1. unfold renL, renR; f_equal; rasimpl.
        1,2:eapply ren_term_morphism; eauto.
        1,2:unfold pointwise_relation; intros; unfold ">>"; destruct a0; simpl; lia.
    * eapply meta_conv. 1:eapply meta_ctx. 1:eapply  H2.
      ** simpl. unfold renR, renL, P'', B, R'0, P'0, B0, R'1, P'1. f_equal. 1:f_equal.
        *** f_equal. 1:f_equal. 2:f_equal.
            4:f_equal. 5:f_equal. all:rasimpl.
            all:eapply ren_term_morphism; eauto.
            all:unfold pointwise_relation; intros; unfold ">>"; destruct a0; try destruct a0; simpl; lia.
        *** f_equal. 1:f_equal. 1:f_equal. 2:f_equal. 4:f_equal.
            4:f_equal. 4:f_equal. 5:f_equal. all:rasimpl.
            all:eapply ren_term_morphism; eauto.
            all:unfold pointwise_relation; intros; unfold ">>" ; destruct a0 ; try destruct a0; simpl; lia.
      ** unfold P'', P''0, renL, renR. f_equal. all:rasimpl.
        all:eapply ren_term_morphism; eauto.
        all:unfold pointwise_relation; intros; unfold ">>" ; destruct a0 ; try destruct a0; simpl ; lia.
    * eapply conv_heq.
      1:replace ((up_ren renL ⋅ P) <[ (renL ⋅ a)..]) with (renL ⋅ (P <[ a..])) by (rasimpl;reflexivity).
      2:replace ((up_ren renR ⋅ P') <[ (renR ⋅ a')..]) with (renR ⋅ (P' <[ a'..])) by (rasimpl;reflexivity).
      3:replace ((0 .: (1 .: renL >> (S >> S))) ⋅ R) with (up_ren (up_ren renL) ⋅ R) by (rasimpl;reflexivity).
      4:replace ((0 .: (1 .: renR >> (S >> S))) ⋅ R') with (up_ren (up_ren renR) ⋅ R') by (rasimpl;reflexivity).
      3,4:eapply conv_refl.
      3,4:eapply meta_conv.
      1,2,3,5:eauto using type_ren, conv_sym, conv_ren, WellRen_renL, WellRen_renR, typing.
      all:rasimpl;reflexivity.

  - eapply type_inv in h1, h2. dependent destruction h1. dependent destruction h2.
    dependent destruction lvl_eq. clear lvl_eq0.

    edestruct IHhsim1; eauto.
    edestruct IHhsim2; eauto.
    edestruct IHhsim3; eauto.

    eexists. eapply type_conv.
    1:eapply type_heq_obseq.
    7:eapply conv_heq. 9,10:rasimpl; eapply conv_refl.
    1-6:eauto using type_ren, WellRen_renL, WellRen_renR.
    1:replace (Sort prop) with (renL ⋅ (Sort prop)) by reflexivity.
    2:replace (Sort prop) with (renR ⋅ (Sort prop)) by reflexivity.
    1-4:eauto 8 using conv_sym, conv_ren, type_ren, typing, WellRen_renL, WellRen_renR.

  - eapply type_inv in h2 as h2'; dependent destruction h2'. subst.
    edestruct (IHhsim _ _ _ _ _ hctx h1 a_Wt).
    eexists. 
    eapply type_heq_trans.
    4:eapply H0.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_renL, WellRen_renR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_renR.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    7:rewrite heq_ren; reflexivity.
    1:eapply type_heq_cast. 3:exact e_Wt.
    all:eauto using conv_sym, conv_refl, conversion.
  - eapply type_inv in h1 as h1'; dependent destruction h1'. subst.
    destruct (IHhsim _ _ _ _ _ hctx a_Wt h2).
    eexists. 
    eapply type_heq_trans.
    5:eapply H0.
    all: try solve [ eapply type_ren; 
      eauto using WellRen_renL, WellRen_renR, validity_ty_ctx ].
    eapply type_ren.
    3:eapply WellRen_renL.
    2:eauto using validity_ty_ctx.
    1:eapply type_conv. 2:eapply conv_heq.
    7:rewrite heq_ren; reflexivity.
    1:eapply type_heq_sym, type_heq_cast.
    5:eapply e_Wt.
    all:eauto using conv_sym, conv_refl, typing.
Qed.


Fixpoint get_entry n Γ :=
  match Γ, n with 
  | nil, _ => (prop, Nat) (* junk *)
  | cons (l, A) Γ, 0 => (l, S ⋅ A)
  | cons _ Γ, S n => 
    let (l, A) := get_entry n Γ in
      (l, S ⋅ A)
    end.
  
Definition get_tail Γ : ctx :=
  match Γ with  
  | cons _ Γ => Γ
  | nil => nil (* junk *)
  end.

Definition pack_refl Γ n :=
  let X := get_entry (n / 3) Γ in
  match n mod 3 with 
  | 0 => heq_refl (fst X) (snd X) (var (n / 3))
  | _ => var (n / 3)
  end.

Lemma mod_aux0 x : (0 + 3 * x) mod 3 = 0.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.

Lemma mod_aux1 x : (1 + 3 * x) mod 3 = 1.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.


Lemma mod_aux2 x : (2 + 3 * x) mod 3 = 2.
Proof.
  rewrite Nat.add_mod by lia. 
  replace (3 * x) with (x * 3) by lia.
  rewrite Nat.mod_mul.
  2:eauto.
  simpl. eauto.
Qed.

Lemma comp_refl_renL' Γ x :
  (pack_refl Γ (renL x)) = var x.
Proof.
  unfold pack_refl, renL. rewrite mod_aux2. 
  replace (2 + 3 * x) with (x * 3 + 2) by lia.
  rewrite Nat.div_add_l by lia.  simpl. replace (x + 0) with x by lia. reflexivity.
Qed.

Lemma comp_refl_renL Γ :
  pointwise_relation _ eq (renL >> pack_refl Γ) var.
Proof.
  unfold pointwise_relation. intros. eapply comp_refl_renL'.
Qed.


Lemma comp_refl_renR' Γ x :
  (pack_refl Γ (renR x)) = var x.
Proof.
  unfold pack_refl, renR. rewrite mod_aux1. 
  replace (1 + 3 * x) with (x * 3 + 1) by lia.
  rewrite Nat.div_add_l by lia.  simpl. replace (x + 0) with x by lia. reflexivity.
Qed.

Lemma comp_refl_renR Γ :
  pointwise_relation _ eq (renR >> pack_refl Γ) var.
Proof.
  unfold pointwise_relation. intros. eapply comp_refl_renR'.
Qed.

Lemma aux_match_nat {A B} (f : A -> B) (n : nat) p0 ps :
  f (match n with 
  | 0 => p0 
  | S n => ps n end)
  = match n with 
  | 0 => f p0 
  | S n => f (ps n) end.
Proof.
  destruct n; reflexivity.
Qed.

Lemma aux_match_nat2 {A} (n : nat) (p0 p0':A) ps ps' :
  p0 = p0' -> 
  (forall x, ps x = ps' x) ->
  match n with 
  | 0 => p0 
  | S n => ps n end
  = match n with 
  | 0 => p0' 
  | S n => ps' n end.
Proof.
  intros. destruct n; eauto.
Qed.

Lemma fun_snd {A B C} (f:B -> C) (t : A * B): 
  f (snd t) = snd (let (a, b) := t in (a, f b)).
Proof.
  destruct t. reflexivity.
Qed.
Lemma fun_fst {A B C} (f:B -> C) (t : A * B): 
  fst t = fst (let (a, b) := t in (a, f b)).
Proof.
  destruct t. reflexivity.
Qed.
Lemma snd_get_entry n Γ l A :
  snd (get_entry (S n) (Γ ,, (l, A))) = S ⋅ (snd (get_entry n Γ)).
Proof.
  simpl. symmetry. eapply fun_snd.
Qed.

Lemma fst_get_entry n Γ l A :
  fst (get_entry (S n) (Γ ,, (l, A))) = fst (get_entry n Γ).
Proof.
  simpl. symmetry. eapply fun_fst.
Qed.

Lemma commute_renL_S A (ρ : nat -> A) : 
  pointwise_relation _ eq (↑ >> (renL >> ρ)) (renL >> (↑ >> (↑ >> (↑ >> ρ)))).
Proof.
  unfold pointwise_relation. intros.
  unfold ">>", "↑", renL. f_equal. lia.
Qed.

Lemma commute_renR_S A (ρ : nat -> A) : 
  pointwise_relation _ eq (↑ >> (renR >> ρ)) (renR >> (↑ >> (↑ >> (↑ >> ρ)))).
Proof.
  unfold pointwise_relation. intros.
  unfold ">>", "↑", renR. f_equal. lia.
Qed.

Lemma pack_refl_Wt Γ : 
  ⊢p Γ -> Γ ⊢ps pack_refl Γ : pack Γ Γ.
Proof.
  intros. induction H.
  1:econstructor.
  simpl. econstructor. 1:econstructor. 1:econstructor.
  - rewrite autosubst_simpl_WellSubst.
    1:eapply WellSubst_weak. 1:eapply IHctx_typing.
    1:assumption.
    econstructor. unfold pointwise_relation. intros.
    unfold ">>".
    unfold pack_refl.
    replace (↑ (↑ (↑ a)) mod 3) with (a mod 3).
    2:{ unfold "↑".
        replace (S (S (S a))) with (3 + a) by lia.
        rewrite Nat.add_mod. 2:lia. 
        change (3 mod 3) with (1 * 3 mod 3).
        rewrite Nat.mod_mul. 2:lia.
        symmetry.
        rewrite Nat.mod_small.
        1:lia.
        change (0 + a mod 3) with (a mod 3).
        eapply Nat.mod_upper_bound. lia. }
    rewrite (aux_match_nat (fun x => S ⋅ x)).
    eapply aux_match_nat2.
    * rewrite ren_heq_refl. f_equal.
      3:{ unfold "↑". 
          change (S ⋅ (var (a / 3))) with (var (1 + a / 3)).
          replace (S (S (S a)) / 3) with (1 + a /3). 1:reflexivity.
          change (S (S (S a))) with (1 * 3 + a).
          rewrite Nat.div_add_l. 2:lia.
          reflexivity. }
      ** replace (↑ (↑ (↑ a)) / 3) with (S (a / 3)).
         2:unfold "↑". 2:replace (S (S (S a))) with (1*3 + a) by lia.
         2:rewrite Nat.div_add_l. 2-3:lia.
         rewrite fst_get_entry. reflexivity.
      ** replace (↑ (↑ (↑ a)) / 3) with (S (a / 3)).
         2:unfold "↑". 2:replace (S (S (S a))) with (1*3 + a) by lia.
         2:rewrite Nat.div_add_l. 2-3:lia.
         rewrite snd_get_entry. reflexivity.
    * intros. unfold "↑". change (S ⋅ (var (a /3))) with (var (1 + a /3)).
      replace (S (S (S a)) / 3) with (1 + a / 3). 1:reflexivity.
      replace (S (S (S a))) with (1 * 3 + a) by lia.
      rewrite Nat.div_add_l. 1:reflexivity. lia.
  - ssimpl. setoid_rewrite <- commute_renL_S.
    setoid_rewrite comp_refl_renL.
    change (pack_refl (Γ,, (l, A)) (↑ (↑ 0))) with (var 0).
    econstructor. 1:eauto using ctx_typing.
    1:eapply varty_meta. 1:econstructor. rasimpl. reflexivity.
  - ssimpl. setoid_rewrite <- commute_renR_S.
    setoid_rewrite comp_refl_renR.
    change (pack_refl (Γ,, (l, A)) (↑ (↑ 0))) with (var 0).
    econstructor. 1:eauto using ctx_typing.
    1:eapply varty_meta. 1:econstructor. rasimpl. reflexivity.
  - rewrite  heq_subst. rasimpl.  setoid_rewrite <- commute_renR_S.  setoid_rewrite <- commute_renL_S.
    setoid_rewrite comp_refl_renL. setoid_rewrite comp_refl_renR.
    unfold ">>". unfold pack_refl. simpl. renamify.
    eapply type_heq_refl.
    1:eapply type_ren; eauto using ctx_typing, WellRen_S.
    econstructor; eauto using ctx_typing.
    econstructor.
Qed.



Lemma compat_refl Γ : ctx_compat Γ Γ.
Proof.
  induction Γ.
  1:econstructor.
  destruct a. econstructor; eauto.
Qed.

Corollary sim_heq_same_ctx i Γ t1 t2 A1 A2 :
  t1 ~ t2 →
  Γ ⊢p< ty i > t1 : A1 →
  Γ ⊢p< ty i > t2 : A2 →
  ∃ e, Γ ⊢p< prop > e : heq (ty i) A1 A2 t1 t2.
Proof.
  intros. edestruct sim_heq; eauto using compat_refl.
  eapply subst_ty in H2. 3:eapply pack_refl_Wt.
  2-4:eauto using validity_ty_ctx.
  rewrite heq_subst in H2. rasimpl in H2.
  setoid_rewrite comp_refl_renL in H2.
  setoid_rewrite comp_refl_renR in H2.
  rasimpl in H2.
  eauto.
Qed.


Lemma assoc (f : nat -> nat) (g : nat -> term) (h : term -> term) :
  pointwise_relation _ eq (f >> (g >> h)) ((f >> g) >> h).
Proof.
  unfold pointwise_relation. unfold ">>". reflexivity.
Qed.

Lemma ctx_extend_Wt Γ l A1 A2 :
  Γ ⊢p< Ax l > A1 : Sort l ->
  Γ ⊢p< Ax l > A2 : Sort l ->
  ⊢p Γ -> 
  let Aeq := heq l ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  ⊢p Γ ,, (l, A1) ,, (l, S ⋅ A2) ,, (prop, Aeq).
Proof.
  intros. econstructor.
  1:econstructor.
  1:econstructor.
  all:eauto.
  1:eapply type_ren; eauto using WellRen_S, ctx_typing.
  unfold Aeq. eapply type_heq.
  1,2:eapply type_ren; eauto using WellRen_weak, WellRen_S, ctx_typing, type_ren.
  all:econstructor; eauto using WellRen_weak, WellRen_S, ctx_typing, type_ren.
  all:eapply varty_meta.
  1,3:econstructor. 1:econstructor.
  all:rasimpl;reflexivity.
Qed.

Lemma pack_refl_cons_Wt l A1 A2 Γ : 
  Γ ⊢p< Ax l > A1 : Sort l ->
  Γ ⊢p< Ax l > A2 : Sort l ->
  ⊢p Γ -> 
  let Aeq := heq l ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  Γ ,, (l, A1) ,, (l, S ⋅ A2) ,, (prop, Aeq) ⊢ps (var 0 .: ((var 1) .: ((var 2) .: (pack_refl Γ >> ren_term (S >> S >> S))))) : pack (Γ ,, (l, A1)) (Γ ,, (l, A2)).
Proof.
  intros.
  simpl. econstructor. 1:econstructor. 1:econstructor. 
  all:ssimpl;rasimpl.
  1:eapply WellSubst_weak_three. 1:eapply pack_refl_Wt; eauto.
  1:eapply ctx_extend_Wt; eauto.
  1:{ setoid_rewrite assoc; setoid_rewrite comp_refl_renL.
      rasimpl. econstructor.   1:eapply ctx_extend_Wt; eauto.
      eapply varty_meta.
      1:econstructor. 1:econstructor. 1:econstructor.
      rasimpl; reflexivity. }
  1:{ setoid_rewrite assoc; setoid_rewrite comp_refl_renR.
      rasimpl. econstructor.   1:eapply ctx_extend_Wt; eauto.
      eapply varty_meta.
      1:econstructor. 1:econstructor.
      rasimpl; reflexivity. }
  rewrite heq_subst. ssimpl.
  setoid_rewrite assoc.
  setoid_rewrite comp_refl_renL.
  setoid_rewrite comp_refl_renR.
  ssimpl.
  econstructor.   1:eapply ctx_extend_Wt; eauto.
  eapply varty_meta.
  1:econstructor. unfold Aeq;rewrite heq_ren ;rasimpl;reflexivity.
Qed.

Lemma ctx_extend2_Wt Γ i j A1 A2 B1 B2 :
  Γ ,, (i, A1) ⊢p< Ax j > B1 : Sort j ->
  Γ ,, (i, A2) ⊢p< Ax j > B2 : Sort j ->
  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  let Beq := heq j ((S >> S >> S >> S) ⋅ B1) ((up_ren S >> S >> S >> S) ⋅ B2) (var 1) (var 0) in
  ⊢p Γ ,, (i, A1) ,, (i, S ⋅ A2),, (prop, Aeq) ,, (j, (S >> S) ⋅ B1) ,, (j,  (up_ren S >> S >> S) ⋅ B2) ,, (prop, Beq).
Proof.
  intros.
  assert (⊢p ((Γ,, (i, A1)),, (i, S ⋅ A2)),, (prop, Aeq))  by 
    (eapply validity_ty_ctx in H,H0; inversion H; inversion H0; eapply ctx_extend_Wt; eauto).
  econstructor.
  1:econstructor.
  1:econstructor.
  1:eassumption.
  1,2:eapply type_ren; eauto using WellRen_weak, WellRen_S, ctx_typing, type_ren, WellRen_up.
  eapply type_heq; eauto.
  1,2:eapply type_ren; eauto 12 using WellRen_weak, WellRen_S, ctx_typing, type_ren, WellRen_up.
  1,2:econstructor.
  1,3:eauto 12 using WellRen_weak, WellRen_S, ctx_typing, type_ren, WellRen_up.
  1,2:eapply varty_meta.
  1,3:econstructor. 1:econstructor.
  all:rasimpl;reflexivity.
Qed.


Lemma renL_jump (a b c : term) σ :
  pointwise_relation nat eq (renL >> (a .: (b .: (c .: σ)))) (c .: (renL >> σ)).
Proof.
  unfold pointwise_relation. intros.
  destruct a0.
  1:unfold ">>";simpl;reflexivity.
  unfold ">>". simpl. unfold renL.
  f_equal. lia.
Qed.

Lemma renR_jump (a b c : term) σ :
  pointwise_relation nat eq (renR >> (a .: (b .: (c .: σ)))) (b .: (renR >> σ)).
Proof.
  unfold pointwise_relation. intros.
  destruct a0.
  1:unfold ">>";simpl;reflexivity.
  unfold ">>". simpl. 
  replace ((a0 + S (a0 + S (a0 + 0)))) with (S a0 + (a0 + S (a0 + 0))) by lia. simpl. 
  unfold renR.
  f_equal. lia.
Qed.


Corollary sim_heq_same_ctx_cons i l Γ t1 t2 B1 B2 A1 A2 :
  t1 ~ t2 →
  Γ ,, (l, A1) ⊢p< ty i > t1 : B1 →
  Γ ,, (l, A2) ⊢p< ty i > t2 : B2 →
  let Aeq := heq l ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  ∃ e, Γ ,, (l, A1) ,, (l, S ⋅ A2) ,, (prop, Aeq) ⊢p< prop > 
    e : heq (ty i) ((S >> S) ⋅ B1) ((up_ren S >> S) ⋅ B2) ((S >> S) ⋅ t1) ((up_ren S >> S) ⋅ t2).
Proof.
  intros. edestruct sim_heq.
  3:eapply H0. 3:eapply H1. 2:eapply H. 1:eauto using ctx_compat, compat_refl.

  eapply validity_ty_ctx in H0 as h0. dependent destruction h0.
  eapply validity_ty_ctx in H1 as h1. dependent destruction h1. clear h0 h1.
  eapply subst_ty in H2.
  3:eapply pack_refl_cons_Wt; eauto using validity_ty_ctx.
  2:eapply ctx_extend_Wt; eauto using validity_ty_ctx.
  2:reflexivity.
  rewrite heq_subst in H2. rasimpl in H2. 
  setoid_rewrite renL_jump in H2.
  setoid_rewrite assoc in H2. setoid_rewrite comp_refl_renL in H2.
  setoid_rewrite renR_jump in H2.
  setoid_rewrite assoc in H2. setoid_rewrite comp_refl_renR in H2.
  asimpl in H2.
  eexists. eapply meta_conv.
  1:eapply H2.
  1:f_equal; rasimpl.
  all:substify.
  all:eapply subst_term_morphism; eauto.
  all:unfold pointwise_relation; intros; destruct a; simpl; eauto.
Qed.


Corollary sim_heq_same_ctx_cons2 i j n Γ t1 t2 C1 C2 B1 B2 A1 A2 :
  t1 ~ t2 →
  Γ ,, (i, A1) ,, (j, B1) ⊢p< ty n > t1 : C1 →
  Γ ,, (i, A2) ,, (j, B2) ⊢p< ty n > t2 : C2 →

  let Aeq := heq i ((S >> S) ⋅ A1) ((S >> S) ⋅ A2) (var 1) (var 0) in
  let Beq := heq j ((S >> S >> S >> S) ⋅ B1) ((up_ren S >> S >> S >> S) ⋅ B2) (var 1) (var 0) in
  exists e,
    Γ ,, (i, A1) ,, (i, S ⋅ A2),, (prop, Aeq) 
      ,, (j, (S >> S) ⋅ B1) ,, (j,  (up_ren S >> S >> S) ⋅ B2) ,, (prop, Beq)
      ⊢p< prop > e : heq (ty n) ((up_ren (S >> S) >> S >> S) ⋅ C1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ C2) 
        ((up_ren (S >> S) >> S >> S) ⋅ t1) ((up_ren (up_ren S >> S >> S) >> S) ⋅ t2).
Proof.
  intros. 
  eapply validity_ty_ctx in H0 as H0'. dependent destruction H0'. clear H0'.
  eapply validity_ty_ctx in H1 as H1'. dependent destruction H1'. clear H1'.
  eapply validity_ty_ctx in H2 as H2'. dependent destruction H2'. clear H2'.
  eapply validity_ty_ctx in H3 as H3'. dependent destruction H3'. clear H3'.

  eapply ctx_extend2_Wt in H3 as ctx_ext2. 2:eapply H2.
  eapply sim_heq in H; eauto.
  2:eauto using ctx_compat, compat_refl.
  destruct H.
  eapply subst_ty in H.
  3:simpl.
  3:eapply WellSubst_up_two.
  3:eapply WellSubst_up_two.
  3:eapply WellSubst_up_two.
  3:eapply pack_refl_Wt; eauto. 
  all:eauto using validity_ty_ctx.
  all:rasimpl; try rewrite heq_subst; try rewrite heq_ren; rasimpl.
  1,2:setoid_rewrite comp_refl_renL; rasimpl.
  1,3:setoid_rewrite assoc; setoid_rewrite comp_refl_renR; rasimpl.
  2,3:reflexivity.
  1: eauto using ctx_typing, type_ren, WellRen_S, validity_ty_ctx.
  1,2:setoid_rewrite assoc; setoid_rewrite comp_refl_renL; setoid_rewrite comp_refl_renR.
  2:unfold Aeq; rasimpl; reflexivity.
  2:setoid_rewrite renL_jump; setoid_rewrite assoc; setoid_rewrite comp_refl_renL; rasimpl.
  2:substify; eapply subst_term_morphism; eauto. 2:unfold pointwise_relation; intro x'; destruct x'; reflexivity.
  all:try setoid_rewrite renL_jump. all:try setoid_rewrite renL_jump.
  all:try setoid_rewrite renR_jump. all:try setoid_rewrite renR_jump.
  1:replace ((λ x0 : nat, x0) >> pack_refl Γ) with (pack_refl Γ) by (rasimpl;reflexivity).
  all:setoid_rewrite assoc; try setoid_rewrite comp_refl_renL; try setoid_rewrite comp_refl_renR.
  all:rasimpl.
  3:substify;ssimpl;reflexivity.
  3:unfold Beq;substify;ssimpl; f_equal.
  3:eapply subst_term_morphism; eauto. 3:unfold pointwise_relation; intros x'; destruct x'; eauto.
  3:f_equal;substify;ssimpl; try reflexivity.
  3,4:eapply subst_term_morphism; eauto. 3,4:unfold pointwise_relation; intros x'; destruct x';try destruct x'; eauto.
  1:{ 
    dependent destruction ctx_ext2.
    dependent destruction ctx_ext2.
    replace (B1 <[ (var 2) .: (S >> (S >> S)) >> var]) with ((S >> S) ⋅ B1). 1:eassumption.
    substify; ssimpl. eapply subst_term_morphism; eauto. unfold pointwise_relation; intros x'; destruct x'; eauto. }
  1:{ 
    assert (forall x y, x =y -> ⊢p x -> ⊢p y) by (intros; subst; eassumption).
    eapply H6. 2:eapply ctx_ext2.
    f_equal. 1:f_equal. 1:f_equal. 3:f_equal. 3:f_equal. 
    all:substify; ssimpl;eapply subst_term_morphism; eauto. all:unfold pointwise_relation; intros x'; destruct x'; eauto. }
Qed.