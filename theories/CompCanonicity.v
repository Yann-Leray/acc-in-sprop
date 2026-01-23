

From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.
From AccInSProp
Require Import core unscoped AST SubstNotations RAsimpl AST_rasimpl
    Util BasicAST Typing BasicMetaTheory Reduction Fundamental LRDef.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Import CombineNotations.

Reserved Notation "t ---> u" (at level 50, u at next level).


(* Instead of introducing a new inductive type to represent the non-annotated syntax,
  we reuse the fully-annotated syntax by replacing annotations by some junk term *)
Definition Box := Nat.
Definition boxlvl := prop.

Definition appu t u := app boxlvl boxlvl Box Box t u.
Definition lamu t := lam boxlvl boxlvl Box Box t.
Definition recu P pzero psucc t := rec boxlvl P pzero psucc t.
Definition accelu P p a := accel boxlvl boxlvl Box Box P p a Box.
Definition castu A B t := cast boxlvl A B Box t.
Definition Piu A B := Pi boxlvl boxlvl A B.
Definition accu A R a := acc boxlvl A R a.
Definition obsequ A a b := obseq boxlvl A a b.


Fixpoint erasure t :=
    match t with
    | var i => var i
    | assm c => assm c
    | lam _ _ _ _ t => lamu (erasure t)
    | app _ _ _ _ t u => appu (erasure t) (erasure u)
    | Pi _ _ A B => Piu (erasure A) (erasure B)
    | zero => zero
    | succ t => succ (erasure t)
    | rec _ P pzero psucc t =>
        recu (erasure P) (erasure pzero) (erasure psucc) (erasure t)
    | Nat => Nat
    | accel _ _ _ _ P p a _ =>
        accelu (erasure P) (erasure p) (erasure a)
    | Sort i => Sort i
    | acc _ A R a => accu (erasure A) (erasure R) (erasure a)
    | obseq _ A a b => obsequ (erasure A) (erasure a) (erasure b)
    | cast i A B e t => castu (erasure A) (erasure B) (erasure t)
    | _ => Nat
    end.

Inductive red_untyped : term -> term -> Prop :=
| redu_app t t' u :
    t ---> t' ->
    appu t u ---> appu t' u

| redu_beta t u :
    appu (lamu t) u ---> t <[ u.. ]

| redu_rec P p_zero p_succ n n' :
    n ---> n' ->
    recu P p_zero p_succ n ---> recu P p_zero p_succ n'

| redu_rec_zero P p_zero p_succ :
    recu P p_zero p_succ zero ---> p_zero

| redu_rec_succ P p_zero p_succ n :
    recu P p_zero p_succ (succ n) ---> p_succ <[  (recu P p_zero p_succ n) .: n ..]

| redu_accel a P p :
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t1 := accelu Pwk pwk (var 1) in
    let t3 := lamu t1 in
    let t5 := lamu t3 in
    accelu P p a ---> p <[ t5 .: a ..]

| redu_cast1 A A' B a :
    A ---> A' ->
    castu A B a ---> castu A' B a

| redu_cast2 A B B' a :
    val A ->
    B ---> B' ->
    castu A B a ---> castu A B' a

| redu_cast_nat t :
    castu Nat Nat t ---> t

| redu_cast_sort i t :
    castu (Sort i) (Sort i) t ---> t

| redu_cast_pi A1 A2 B1 B2 f :
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let t1 := castu A2' A1' (var 0) in
    let t2 := appu (S ⋅ f) t1 in
    let t3 := castu (B1 <[t1.: S >> var]) B2 t2 in
    let t4 := lamu t3 in
    castu (Piu A1 B1) (Piu A2 B2) f ---> t4

where "t ---> u" := (red_untyped t u).


Lemma ren_erasure t ρ :
    erasure (ρ ⋅ t) = ρ ⋅ (erasure t).
Proof.
    generalize ρ. clear ρ.
    induction t; simpl; intuition eauto.
    all: try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3;
    try rewrite IHt4; try rewrite IHt4;
    try rewrite IHt5; try rewrite IHt6; try reflexivity.
Qed.

Lemma ren_term_erasure ρ :
    pointwise_relation _ eq
    (ren_term ρ >> erasure) (erasure >> ren_term ρ).
Proof.
    unfold pointwise_relation. intros. unfold ">>".
    rewrite ren_erasure. reflexivity.
Qed.

Lemma subst_erasure t σ :
    erasure (t <[ σ ]) = (erasure t) <[ fun x => erasure (σ x)].
Proof.
    assert (pointwise_relation _ eq
            (ren_term S >> (ren_term S >> erasure))
            (ren_term (S >> S) >> erasure)) as aux.
        { unfold pointwise_relation. intros.  unfold ">>".
          ssimpl. reflexivity. }

    generalize σ. clear σ.
    induction t; intros; simpl; eauto.
    - unfold Piu. f_equal.
      rewrite IHt1; eauto.
      rewrite IHt2; eauto. unfold up_term_term. ssimpl. simpl.
      setoid_rewrite ren_term_erasure. reflexivity.
    - unfold lamu. f_equal.
      rewrite IHt3. unfold up_term_term. ssimpl. simpl.
      setoid_rewrite ren_term_erasure. reflexivity.
    - unfold appu. f_equal.
      rewrite IHt3. reflexivity.
      rewrite IHt4. reflexivity.
    - rewrite IHt. reflexivity.
    - unfold recu. f_equal.
      * rewrite IHt1. unfold up_term_term. ssimpl. simpl.
        setoid_rewrite ren_term_erasure. reflexivity.
      * rewrite IHt2. reflexivity.
      * rewrite IHt3. unfold up_term_term. ssimpl. fold erasure.
        setoid_rewrite aux. setoid_rewrite ren_term_erasure. reflexivity.
      * rewrite IHt4. reflexivity.
    - unfold accu. f_equal.
      * rewrite IHt1. reflexivity.
      * rewrite IHt2. unfold up_term_term. ssimpl. fold erasure.
        setoid_rewrite aux. setoid_rewrite ren_term_erasure. reflexivity.
      * rewrite IHt3. reflexivity.
    - unfold accelu. f_equal.
      * rewrite IHt3. unfold up_term_term. ssimpl. simpl.
      setoid_rewrite ren_term_erasure. reflexivity.
      * rewrite IHt4. unfold up_term_term. ssimpl. fold erasure.
        setoid_rewrite aux. setoid_rewrite ren_term_erasure. reflexivity.
      * rewrite IHt5. reflexivity.
    - unfold obsequ. f_equal.
      * rewrite IHt1. reflexivity.
      * rewrite IHt2. reflexivity.
      * rewrite IHt3. reflexivity.
    - unfold castu. f_equal.
      * rewrite IHt1. reflexivity.
      * rewrite IHt2. reflexivity.
      * rewrite IHt4. reflexivity.
Qed.

Lemma erasure_cons u x :
    erasure ((u .. ) x) = ((erasure u) ..) x.
Proof.
    destruct x.
    -  reflexivity.
    -  reflexivity.
Qed.

Lemma erasure_cons2 u v x :
    erasure ((u .: v .. ) x) = ((erasure u).:(erasure v) ..) x.
Proof.
    destruct x.
    -  reflexivity.
    -  destruct x; reflexivity.
Qed.

Lemma redu_meta t u u' :
    t ---> u ->
    u = u' ->
    t ---> u'.
Proof.
    intros. subst. auto.
Qed.

Lemma red_erasure Γ i t u A :
    Γ ⊢d< ty i > t --> u : A ->
    (erasure t) ---> (erasure u).
Proof.
    intros. dependent induction H; unfold Ru in *;
    intros; simpl;
    try rewrite subst_erasure;
    try setoid_rewrite erasure_cons;
    try setoid_rewrite erasure_cons2;
    eauto using red_untyped.
    - eapply redu_meta. econstructor.
      simpl.
      unfold t5, t4, t3, t2, t1, t0, pwk, Pwk, Rwk, Awk, lamu, lamu, accu.
      eapply subst_term_morphism; eauto.
      unfold pointwise_relation. intros. destruct a0.
      * simpl. f_equal. f_equal. f_equal.
        unfold up_ren. rewrite ren_erasure. reflexivity.
        unfold up_ren. rewrite ren_erasure. reflexivity.
      * simpl. reflexivity.
    - econstructor. eapply IHred. reflexivity.
    - econstructor. 2:eapply IHred; reflexivity.
      destruct A; unfold val in *; eauto.
    - unfold Piu, t1, A1', A2', B1', B2', castu. eapply redu_meta.
      eapply redu_cast_pi. unfold castu. simpl.
      f_equal.  f_equal.
      eapply subst_term_morphism; eauto.
      unfold pointwise_relation. intros a.
      destruct a. simpl. unfold castu.
      setoid_rewrite ren_erasure. reflexivity.
      reflexivity.
      setoid_rewrite ren_erasure. reflexivity.
Qed.


Reserved Notation "t -->> u" (at level 50, u at next level).

Inductive reddu : term -> term -> Prop :=
  | reddu_refl t : t -->> t
  | reddu_step t u v : t ---> v -> v -->> u -> t -->> u
where "t -->> t'" := (reddu t t').

Lemma redd_erasure Γ i t u A :
    Γ ⊢d< ty i > t -->> u : A ->
    (erasure t) -->> (erasure u).
Proof.
    intros. dependent induction H; eauto using reddu, red_erasure.
Qed.

Derive Signature for red_untyped.

Lemma redu_fun t u v :
    t ---> u ->
    t ---> v ->
    u = v.
Proof.
    intro. generalize v. clear v.
    dependent induction H; intros; eauto using red_untyped.
    - dependent destruction H0.
      + erewrite IHred_untyped; eauto.
      + dependent destruction H.
    - dependent destruction H.
      dependent destruction H.
      reflexivity.
    - dependent destruction H0.
      + erewrite IHred_untyped; eauto.
      + dependent destruction H.
      + dependent destruction H.
    - dependent destruction H.
      dependent destruction H.
      reflexivity.
    - dependent destruction H.
      dependent destruction H.
      reflexivity.
    - dependent destruction H. reflexivity.
    - dependent destruction H0.
      + erewrite IHred_untyped; eauto.
      + destruct A; inversion H0; inversion H.
      + dependent destruction H.
      + dependent destruction H.
      + dependent destruction H.
    - dependent destruction H1.
      + destruct A; inversion H1; inversion H.
      + erewrite IHred_untyped; eauto.
      + dependent destruction H0.
      + dependent destruction H0.
      + dependent destruction H0.
    - dependent destruction H.
      + dependent destruction H.
      + dependent destruction H0.
      + reflexivity.
    - dependent destruction H.
      + dependent destruction H.
      + dependent destruction H0.
      + reflexivity.
    - dependent destruction H.
      + dependent destruction H.
      + dependent destruction H0.
      + reflexivity.
Qed.

Lemma reddu_fun t u v :
    t -->> u -> val u ->
    t -->> v -> val v ->
    u = v.
Proof.
    intros.  generalize v H1 H2. clear v H1 H2.
    dependent induction H.
    - intros. dependent destruction H1.
      reflexivity.
      destruct t; dependent destruction H; dependent destruction H0.
    - intros. dependent destruction H2.
      destruct t; dependent destruction H; dependent destruction H3.
      eapply redu_fun in H; eauto. subst.
      eapply IHreddu in H4; eauto.
Qed.


Inductive eval : term -> nat -> Prop :=
| eval_0 t :
    t -->> zero ->
    eval t 0
| eval_S t u n :
    t -->> succ u ->
    eval u n ->
    eval t (S n).

Lemma eval_red_untyped n :
    ∙ ⊢d< ty 0 > n : Nat ->
    exists k, eval (erasure n) k.
Proof.
    intros.
    eapply canonicity_red in H as (k & lr).
    induction lr.
    - destruct H. eapply redd_erasure in H.
      exists 0. econstructor. eauto.
    - destruct IHlr as (k' & ev).
      exists (S k'). destruct H.
      eapply redd_erasure in H.
      econstructor; eauto.
Qed.


Derive Signature for ϵNat.
Derive Signature for eval.

Lemma eval_red_untyped_correct k n :
    ∙ ⊢d< ty 0 > n : Nat ->
    eval (erasure n) k ->
    ∙ ⊢d< ty 0 > n ≡ mk_Nat k : Nat.
Proof.
    intros nWt eval.
    dependent induction eval;
    eapply canonicity_red in nWt as temp;
    destruct temp as (k' & lr).
    - dependent destruction lr.
      * destruct H0. eapply redd_to_conv in H0. eauto.
      * destruct H0. eapply redd_erasure in H0.
        eapply reddu_fun in H; eauto. 2:simpl;eauto.
        inversion H.
    - dependent destruction lr.
      * destruct H0. eapply redd_erasure in H0.
        eapply reddu_fun in H; eauto. 2:simpl;eauto.
        inversion H.
      * destruct H0. eapply redd_erasure in H0 as H0'.
        eapply reddu_fun in H as temp; eauto.
        2:simpl;eauto.
        dependent destruction temp.
        eapply redd_to_conv in H0 as H0''.
        eapply conv_trans.
        exact H0''.
        eapply conv_succ.
        eapply IHeval. 2:reflexivity.
        eapply redd_to_conv, validity_conv_right, type_inv in H0. 
        dependent destruction H0.
        eauto.
Qed.

Lemma eval_functional t n m :
  eval t n -> eval t m -> n = m.
Proof.
  intro. generalize m. clear m. dependent induction H.
  - intros. dependent destruction H0; eauto.
    eapply reddu_fun in H0. 2:eapply H. 
    inversion H0. all: eauto.
  - intros. dependent destruction H1; eauto.
    * eapply reddu_fun in H. 2:eapply H1. 
      inversion H. all: eauto.
    * eapply reddu_fun in H. 2:eapply H1.
      2,3:eauto. dependent destruction H.
      eapply IHeval in H2. subst. reflexivity.
Qed.


Theorem computational_canonicity n : 
    ∙ ⊢d< ty 0 > n : Nat ->
    exists k, eval (erasure n) k /\ 
    ∙ ⊢d< ty 0 > n ≡ mk_Nat k : Nat /\
    (forall k', eval (erasure n) k' -> k = k').
Proof.
  intros. eapply eval_red_untyped in H as H'. destruct H'.
  eapply eval_red_untyped_correct in H0 as H1; eauto.
  eexists. split. 2:split. 
  1,2:eassumption.
  intros. eauto using eval_functional.
Qed.