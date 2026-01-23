(* adapted from a proof by Valentin Blot *)

Set Universe Polymorphism.

Open Scope type_scope.

From SystemF Require Import sum Observational Logic Arith List Substitution Sigma.

(** * Confluence of pure λ-calculus

  In the following, we prove confluence of pure λ-calculus, but
  this is completely independent from the strong normalization proof.
  We follow the proof of Krivine's book "Lambda-Calculus Types and
  Models". *)

Section ReflTransClosure.
Variable A : Type.
(** Here are the definitions of confluence and reflexive
  transitive closure for arbitrary relations *)
Definition confluent (R : A -> A -> SProp) : SProp :=
  forall (t t' t'' : A),
    R t t' ->  R t t'' -> Σ t''' : A, prod (R t' t''') (R t'' t''').
Inductive refl_trans_closure (R : A -> A -> SProp) : A -> A -> SProp :=
  | Refl : forall (t : A), refl_trans_closure R t t
  | Trans : forall (t t' t'' : A), (R t t') -> refl_trans_closure R t' t'' -> refl_trans_closure R t t''.
Section Confluent.
Variable R : A -> A -> SProp.
Infix "⇾" := R.
Infix "⇾*" := (refl_trans_closure R).
Lemma refl_trans_refl : forall (t : A), t ⇾* t.
Proof.
intro t.
apply Refl.
Qed.
Lemma refl_trans_trans : forall (t t' t'' : A),
  t ⇾* t' -> t' ⇾* t'' -> t ⇾* t''.
Proof.
intros t t' t'' Hred Hred'.
induction Hred as [ t | t0 t t' Hred0 Hred IH ].
*assumption.
*eapply Trans.
 +apply Hred0.
 +apply IH.
  assumption.
Qed.
Lemma refl_trans_confluent : confluent R -> confluent (refl_trans_closure R).
Proof.
intro Hconfl.
assert (forall (t : A) (t' : A) (t'' : A),
  t ⇾* t' -> t ⇾ t'' -> (Σ t''' : A, t' ⇾ t''' /\ t'' ⇾* t''') : SProp) as H.
*intros t t' t'' Hred'.
 revert t''.
 induction Hred' as [ t | t0 t0' t' Hred0' Hred' IH ]; intros t0'' Hred0''.
 +exists t0''.
  split.
  -assumption.
  -apply Refl.
 +edestruct Hconfl as [ t0''' [ Hred00' Hred00'' ] ]; [ exact Hred0' | exact Hred0'' | ]; clear Hred0' Hred0''.
  edestruct IH as [ t''' [ Hred000' Hred000'' ] ]; [ exact Hred00' | ]; clear IH.
  exists t'''.
  split.
  -assumption.
  -eapply Trans; [ exact Hred00'' | exact Hred000'' ].
*intros t t' t'' Hred' Hred''.
 revert t' Hred'.
 induction Hred'' as [ t | t0 t0'' t'' Hred0'' Hred'' IH ]; intros t' Hred'.
 +exists t'.
  split.
  -apply Refl.
  -assumption.
 +edestruct H as [ t1' [ Hred1' Hred1'' ] ]; [ exact Hred' | exact Hred0'' | ]; clear H.
  edestruct IH as [ t''' [ Hred2' Hred2'' ] ]; [ exact Hred1'' | ]; clear IH.
  exists t'''.
  split.
  -eapply Trans; [ exact Hred1' | exact Hred2' ].
  -assumption.
Qed.
End Confluent.
Variable R : A -> A -> SProp.
Infix "⇾" := R.
Infix "⇾*" := (refl_trans_closure R).
Variable R' : A -> A -> SProp.
Infix "⇾'" := R'.
Infix "⇾'*" := (refl_trans_closure R').
Lemma refl_trans_incl :
  (forall (t : A) (t' : A), t ⇾ t' -> t ⇾'* t')
   -> (forall (t : A) (t' : A), t ⇾* t' -> t ⇾'* t').
Proof.
intros Hinc t t' Hred.
induction Hred as [ t | t t' t'' Hred Hred' IH ].
*apply Refl.
*eapply refl_trans_trans.
 +apply Hinc.
  exact Hred.
 +assumption.
Qed.
End ReflTransClosure.

Arguments confluent {_} _.
Notation "↑ d t" := (shift _ d t).
Notation " t [ n ↦ u ]" := (substitute _ n t u).
Notation "⇑ d t" := (shift_list _ d t).
Notation " t [[ n ↦ s ]]" := (substitute_list _ n t s).
Notation "p … n -1" := (var_seq _ p n).
(** TermParam is a custom type allowing notations which are specific
  to λ-terms *)
Inductive TermParam :=.
Abbreviation Term := (@MakeTree TermParam).
Notation "# n" := (@Leaf TermParam n).
Notation "'λ' t" := (@Bind TermParam t).
Infix "@" := (@Node TermParam).
(** Our [red0] is Krivine's ρ *)
Inductive red0 : Term -> Term -> SProp :=
  | Ctx_Var0 : forall (n : nat), red0 (#n) (#n)
  | Beta0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (λ t1@t2) (t1'[0↦t2'])
  | Ctx_Abs0 : forall (t t' : Term), red0 t t' -> red0 (λ t) (λ t')
  | Ctx_App0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (t1@t2) (t1'@t2').
Infix "⇾₀" := red0.
Infix "⇾₀*" := (refl_trans_closure _ red0).
Lemma red0_refl : forall (t : Term), t ⇾₀ t.
Proof.
intro t.
induction t as [ n | t IH | t1 IH1 t2 IH2 ].
*apply Ctx_Var0.
*apply Ctx_Abs0; assumption.
*apply Ctx_App0; assumption.
Qed.
Lemma red0_shift : forall (t t' : Term) (d : nat),
  t ⇾₀ t' -> ↑d t ⇾₀ ↑d t'.
Proof.
intros t t' d Hred.
revert d.
induction Hred as [ n | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 | t t' Hred IH | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 ]; intro d.
*apply red0_refl.
*rewrite shift_node, shift_bind, <- shift_substitute2; [| constructor].
 apply Beta0.
 +apply IH1.
 +apply IH2.
*rewrite 2 shift_bind.
 apply Ctx_Abs0.
 apply IH.
*rewrite 2 shift_node.
 apply Ctx_App0.
 +apply IH1.
 +apply IH2.
Qed.
Lemma red0_subst : forall (t1 t1' t2 t2' : Term) (n : nat),
  t1 ⇾₀ t1' -> t2 ⇾₀ t2' ->  t1[n↦t2] ⇾₀ t1'[n↦t2'].
Proof.
intros t1 t1' t2 t2' n Hred1 Hred2.
revert t2 t2' Hred2 n.
induction Hred1 as [ m | t11 t11' t12 t12' Hred11 IH1 Hred12 IH2 | t1 t1' Hred1' IH | t11 t11' t12 t12' Hred11 IH1 Hred12 IH2 ]; intros t2 t2' Hred2 n.
* case (dec_le n m); intro Hdec.
 +rewrite 2 substitute_leaf2; eauto.
  apply Ctx_Var0.
 +case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec. 
  - rewrite Hdec.
    rewrite 2 substitute_leaf1.
    assumption.
  - rewrite 2 substitute_leaf3; eauto.
    apply Ctx_Var0.
*rewrite substitute_node, substitute_bind, substitute_substitute; [|constructor].
 apply Beta0.
 +apply IH1.
  apply red0_shift.
  assumption.
 +apply IH2.
  assumption.
*rewrite 2 substitute_bind.
 apply Ctx_Abs0.
 apply IH.
 apply red0_shift.
 assumption.
*rewrite 2 substitute_node.
 apply Ctx_App0.
 +apply IH1.
  assumption.
 +apply IH2.
  assumption.
Qed.
Lemma red0_confluent : confluent red0.
Proof.
intro t; induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intros t' t'' Hred' Hred''.
*inversion_clear Hred' as [ n1 | | | ].
 inversion_clear Hred'' as [ n2 | | | ].
 exists (#n).
 split; apply Ctx_Var0.
*revert IH.
 inversion_clear Hred' as [ | | t0 t0' Hred0' | ].
 inversion_clear Hred'' as [ | | t0 t0'' Hred0'' | ]; intro IH.
 clear t' t''.
 edestruct IH as [ t''' [ Hred' Hred'' ] ]; [ exact Hred0' | exact Hred0'' | ]; clear IH.
 exists (λ t''').
 split; apply Ctx_Abs0; assumption.
*revert Hred'' IH1 IH2.
 inversion_clear Hred' as [ | t01 t01' t02 t02' Hred01' Hred02' | | t01 t01' t02 t02' Hred01' Hred02' ]; intro Hred''.
 +rename t2 into t02; clear t1 t'.
  inversion_clear Hred'' as [ | t001 t01'' t002 t02'' Hred01'' Hred02'' | | t001 t01'' t002 t02'' Hred01'' Hred02'' ]; intros IH1 IH2; clear t''.
  -edestruct IH1 as [ t01''' [ Hred1' Hred1'' ] ]; [ apply Ctx_Abs0; exact Hred01' | apply Ctx_Abs0; exact Hred01'' | ]; clear IH1.
   revert Hred1''.
   inversion_clear Hred1' as [ | | t001' t001''' Hred001' | ]; intro Hred1''.
   clear t01'''; rename t001''' into t01'''; rename Hred001' into Hred1'.
   inversion_clear Hred1'' as [ | | t001'' t001''' Hred001'' | ].
   rename Hred001'' into Hred1''.
   edestruct IH2 as [ t02''' [ Hred2' Hred2'' ] ]; [ exact Hred02' | exact Hred02'' | ]; clear IH2.
   exists (t01'''[0↦t02''']).
   split; apply red0_subst; assumption.
  -inversion_clear Hred01'' as [ | | t001 t001'' Hred001'' | ].
   clear t01''; rename t001'' into t01''; rename Hred001'' into Hred01''.
   edestruct IH1 as [ t01''' [ Hred1' Hred1'' ] ]; [ apply Ctx_Abs0; exact Hred01' | apply Ctx_Abs0; exact Hred01'' | ]; clear IH1.
   revert Hred1''.
   inversion_clear Hred1' as [ | | t001' t001''' Hred001' | ]; intro Hred1''.
   clear t01'''; rename t001''' into t01'''; rename Hred001' into Hred1'.
   inversion_clear Hred1'' as [ | | t001'' t001''' Hred001'' | ].
   rename Hred001'' into Hred1''.
   edestruct IH2 as [ t02''' [ Hred2' Hred2'' ] ]; [ exact Hred02' | exact Hred02'' | ]; clear IH2.
   exists (t01'''[0↦t02''']).
   split; [ apply red0_subst; assumption | apply Beta0; assumption ].
 +rename t01' into t1'; rename t02' into t2'; rename Hred01' into Hred1'; rename Hred02' into Hred2'; clear t'.
  revert Hred1'.
  inversion_clear Hred'' as [ | t01 t1'' t02 t2'' Hred1'' Hred2'' | | t01 t1'' t02 t2'' Hred1'' Hred2'' ]; intros Hred1' IH1 IH2; clear t''.
  -clear t1; rename t01 into t1.
   edestruct IH2 as [ t2''' [ Hred02' Hred02'' ] ]; [ exact Hred2' | exact Hred2'' | ]; clear IH2.
   inversion_clear Hred1' as [ | | t01 t01' Hred01' | ].
   clear t1'; rename t01' into t1'; rename Hred01' into Hred1'.
   edestruct IH1 as [ t1''' [ Hred01' Hred01'' ] ]; [ apply Ctx_Abs0; exact Hred1' | apply Ctx_Abs0; exact Hred1'' | ]; clear IH1.
   revert Hred01''.
   inversion_clear Hred01' as [ | | t01' t01''' Hred001' | ]; intro Hred01''.
   clear t1'''; rename t01''' into t1'''; rename Hred001' into Hred01'.
   inversion_clear Hred01'' as [ | | t01'' t01''' Hred001'' | ].
   rename Hred001'' into Hred01''.
   exists (t1'''[0↦t2''']).
   split; [ apply Beta0; assumption | apply red0_subst; assumption ].
  -edestruct IH1 as [ t1''' [ Hred01' Hred01'' ] ]; [ exact Hred1' | exact Hred1'' | ].
   edestruct IH2 as [ t2''' [ Hred02' Hred02'' ] ]; [ exact Hred2' | exact Hred2'' | ].
   exists (t1'''@t2''').
   split; apply Ctx_App0; assumption.
Qed.
 (** Our [beta] is Krivine's β₀ *)
Inductive beta : Term -> Term -> SProp :=
  | Beta : forall (t t' : Term), beta ((λ t)@t') (t[0↦t'])
  | Ctx_Abs : forall (t t' : Term), beta t t' -> beta (λ t) (λ t')
  | Ctx_App_l : forall (t1 t1' : Term) (t2 : Term), beta t1 t1' -> beta (t1@t2) (t1'@t2)
  | Ctx_App_r : forall (t1 t2 : Term) (t2' : Term), beta t2 t2' -> beta (t1@t2) (t1@t2').
Infix "⇾" := beta.
Infix "⇾*" := (refl_trans_closure _ beta).
Lemma beta_red0_incl : forall (t t' : Term), t ⇾ t' -> t ⇾₀ t'.
Proof.
intros t t' Hred.
induction Hred as [ t t' | t t' IH | t1 t1' t2 Hred IH | t1 t2 t2' Hred IH ].
*apply Beta0.
 +apply red0_refl.
 +apply red0_refl.
*apply Ctx_Abs0; assumption.
*apply Ctx_App0.
 +assumption.
 +apply red0_refl.
*apply Ctx_App0.
 +apply red0_refl.
 +assumption.
Qed.
Lemma beta_substitute : forall (t t' t'' : Term) (n : nat),
  t ⇾ t' -> t[n↦t''] ⇾ t'[n↦t''].
Proof.
intro t.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros t' t'' n Hred.
*inversion Hred.
*inversion_clear Hred as [ | t''' t'''' Hred' | | ].
 rewrite 2 substitute_bind.
 apply Ctx_Abs.
 apply IH.
 assumption.
*inversion_clear Hred as [ t1' t2' | | t1' t1'' t2' Hred1 | t1' t2' t2'' Hred2 ].
 +rewrite substitute_node, substitute_bind, substitute_substitute;[|constructor].
  apply Beta.
 +rewrite 2 substitute_node.
  apply Ctx_App_l.
  apply IH1.
  assumption.
 +rewrite 2 substitute_node.
  apply Ctx_App_r.
  apply IH2.
  assumption.
Qed.
Lemma shift_beta : forall (t t' : Term) (d : nat),
  ↑d t ⇾ t' -> (Σ t'' : Term, t ⇾ t'' /\ t' ~ ↑d t'') : SProp.
Proof.
intro t; induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros t' d.
*case (le_dec d m); intro Hdec.
 +rewrite shift_leaf1; eauto.
  intro Hred; inversion Hred.
 +rewrite shift_leaf2.
  intro Hred; inversion Hred. now eapply not_le_lt.
*rewrite shift_bind.
 intro Hred; inversion_clear Hred as [ | t'' t''' Hred' | | ].
 clear t'.
 edestruct IH as [ t' [ Hredt' Heqt' ] ]; [ exact Hred' | ].
 exists (λ t').
 split.
 +apply Ctx_Abs.
  assumption.
 +rewrite shift_bind.
  rewrite Heqt'.
  reflexivity.
*rewrite shift_node.
 remember (↑d t1) as t001 eqn:Heqt1; intro Hred; revert Heqt1.
 inversion_clear Hred as [ t01 t02 | | t01 t01' t02 Hred01 | t01 t02 t02' Hred02 ].
 +clear t001 IH1 IH2.
  destruct t1 as [ m | t1 | t11 t12 ].
  - case (le_dec d m); intro Hdec; [ rewrite shift_leaf1 ; eauto| rewrite shift_leaf2 ; eauto ]; try discriminate.
    now apply not_le_lt.
  -rewrite shift_bind.
   intro Heqt1; injection Heqt1; clear Heqt1.
   intro Heqt1; rewrite Heqt1; clear t01 Heqt1.
   exists (t1[0↦t2]).
   split; [ apply Beta | ].
   apply shift_substitute2; constructor.
  -rewrite shift_node; discriminate.
 +intro Heq; rewrite Heq in Hred01; clear t001 Heq IH2.
  edestruct IH1 as [ t1' [ Hred1 Heq1' ] ]; [ exact Hred01 | ]; clear IH1 Hred01.
  rewrite Heq1'; clear t01' Heq1'.
  exists (t1'@t2).
  split.
  -apply Ctx_App_l.
   assumption.
  -rewrite shift_node.
   reflexivity.
 +intro Heq; rewrite Heq; clear t001 Heq IH1.
  edestruct IH2 as [ t2' [ Hred2 Heq2' ] ]; [ exact Hred02 | ]; clear IH2 Hred02.
  rewrite Heq2'; clear t02' Heq2'.
  exists (t1@t2').
  split.
  -apply Ctx_App_r.
   assumption.
  -rewrite shift_node.
   reflexivity.
Qed.
Lemma substitute_leaf_beta : forall (t t' : Term) (p q : nat),
  t[p↦#q] ⇾ t' -> (Σ t'' : Term,  t ⇾ t'' /\ t' ~ t''[p↦#q]) : SProp.
Proof.
intro t; induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros t' p q.
* case (dec_le p m); intro Hdec. 
 +rewrite substitute_leaf2; eauto.
  intro Hred; inversion Hred.
 + case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
   - rewrite Hdec.
     rewrite substitute_leaf1.
     intro Hred; inversion Hred.
  - rewrite substitute_leaf3; eauto.
    intro Hred; inversion Hred.
*rewrite substitute_bind.
 intro Hred; inversion_clear Hred as [ | t'' t''' Hred' | | ].
 clear t'.
 edestruct IH as [ t' [ Hredt' Heqt' ] ]; [ exact Hred' | ].
 exists (λ t').
 split; [ apply Ctx_Abs; exact Hredt' | ].
 rewrite substitute_bind.
 rewrite Heqt'.
 rewrite shift_leaf1; [|constructor].
 reflexivity.
*rewrite substitute_node.
 remember (t1[p↦#q]) as t001 eqn:Heqt1; intro Hred; revert Heqt1.
 inversion_clear Hred as [ t01 t02 | | t01 t01' t02 Hred01 | t01 t02 t02' Hred02 ].
 +clear t001 IH1 IH2.
  destruct t1 as [ m | t1 | t11 t12 ].
  - case (dec_le p m); intro Hdec.
   ++ rewrite substitute_leaf2; eauto. discriminate.
   ++ case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
     +++ rewrite Hdec. rewrite substitute_leaf1. discriminate.
     +++  rewrite substitute_leaf3; eauto; discriminate.
  -rewrite substitute_bind.
   intro Heqt1; injection Heqt1; clear Heqt1.
   intro Heqt1; rewrite Heqt1; clear t01 Heqt1.
   exists (t1[0↦t2]).
   split; [ apply Beta | ].
   apply Eq_sym. apply substitute_substitute. constructor.
  -rewrite substitute_node; discriminate.
 +intro Heq; rewrite Heq in Hred01; clear t001 Heq IH2.
  edestruct IH1 as [ t1' [ Hred1 Heq1' ] ]; [ exact Hred01 | ]; clear IH1 Hred01.
  rewrite Heq1'; clear t01' Heq1'.
  exists (t1'@t2).
  split.
  -apply Ctx_App_l.
   assumption.
  -rewrite substitute_node.
   reflexivity.
 +intro Heq; rewrite Heq; clear t001 Heq IH1.
  edestruct IH2 as [ t2' [ Hred2 Heq2' ] ]; [ exact Hred02 | ]; clear IH2 Hred02.
  rewrite Heq2'; clear t02' Heq2'.
  exists (t1@t2').
  split.
  -apply Ctx_App_r.
   assumption.
  -rewrite substitute_node.
   reflexivity.
Qed.
Lemma beta_cl_leaf : forall (n : nat), #n ⇾* #n.
Proof.
intro n.
apply Refl.
Qed.
Lemma beta_cl_bind : forall (t t' : Term), t ⇾* t' -> λ t ⇾* λ t'.
Proof.
intros t t' Hred.
induction Hred as [ t | t t' t'' Hred Hred' IH ].
*apply Refl.
*eapply Trans.
 +apply Ctx_Abs.
  exact Hred.
 +assumption.
Qed.
Lemma beta_cl_node : forall (t1 t1' t2 t2' : Term),
  t1 ⇾* t1' -> t2 ⇾* t2' -> t1@t2 ⇾* t1'@t2'.
Proof.
intros t1 t1' t2 t2' Hred1.
revert t2 t2'.
induction Hred1 as [ t1 | t1 t1' t1'' Hred1 Hred1' IH1 ]; intros t2 t2' Hred2.
*induction Hred2 as [ t2 | t2 t2' t2'' Hred2 Hred2' IH2 ].
 +apply Refl.
 +eapply Trans.
  -apply Ctx_App_r.
   exact Hred2.
  -apply IH2.
*induction Hred2 as [ t2 | t2 t2' t2'' Hred2 Hred2' IH2 ].
 +eapply Trans.
  -apply Ctx_App_l.
   exact Hred1.
  -apply IH1.
   apply Refl.
 +eapply Trans.
  -apply Ctx_App_r.
   exact Hred2.
  -apply IH2.
Qed.

Lemma red0_beta_cl_incl : forall (t t' : Term), t ⇾₀ t' -> t ⇾* t'.
Proof.
intros t t' Hred.
induction Hred as [ n | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 | t t' Hred IH | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 ].
*apply Refl.
*eapply refl_trans_trans.
 +apply beta_cl_node.
  -apply beta_cl_bind.
   exact IH1.
  -exact IH2.
 +eapply Trans.
  -apply Beta.
  -apply Refl.
*apply beta_cl_bind; assumption.
*apply beta_cl_node; assumption.
Qed.
Lemma red0_beta_equiv : forall (t t' : Term), t ⇾₀* t' <--> t ⇾* t'.
Proof.
intros t t'.
split.
*apply refl_trans_incl.
 apply red0_beta_cl_incl.
*apply refl_trans_incl.
 clear t t'; intros t t' Hred.
 eapply Trans; [ | apply Refl ].
 apply beta_red0_incl; assumption.
Qed.
Lemma beta_cl_confluent : confluent (refl_trans_closure _ beta).
Proof.
assert (confluent (refl_trans_closure _ red0)) as red0_conf.
*apply refl_trans_confluent.
 apply red0_confluent.
*intros t t1 t2.
 intro Hred1; generalize (snd (red0_beta_equiv _ _) Hred1); clear Hred1; intro Hred1.
 intro Hred2; generalize (snd (red0_beta_equiv _ _) Hred2); clear Hred2; intro Hred2.
 edestruct red0_conf as  [ t' Hred ]; [ exact Hred1 | exact Hred2 | ]; clear red0_conf Hred1 Hred2.
 destruct Hred as [ Hred1 Hred2 ].
 exists t'.
 split; apply red0_beta_equiv; assumption.
Qed.

