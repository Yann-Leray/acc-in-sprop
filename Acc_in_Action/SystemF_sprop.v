(* adapted from a proof by Valentin Blot *)

Set Warnings "-level-tolerance".
Set Universe Polymorphism.

Open Scope type_scope.

From SystemF Require Import sum Observational Acc Logic Arith List Substitution Confluence Sigma.

Definition Normalizing : Term -> SProp := Acc (fun t t' => t' ⇾ t).

Definition normInv t (x:Normalizing t): forall (t' : Term), t ⇾ t' -> Normalizing t' := 
  acc_inv _ _ _ x.

Definition NormalizingInd t x : Normalizing t := acc_in _ _ t x. 

Definition Normalizing_rec := acc_el _ (fun t t' => t' ⇾ t).

Lemma normalizing_abs : forall (t : Term), Normalizing (λ t) -> Normalizing t.
Proof.
intros t Hnorm.
remember (λ t) as t' eqn:Heq.
revert t Heq.
induction Hnorm as [ t _ IH ]; intros t' Heq.
apply NormalizingInd.
intros t'' Hred.
eapply IH.
*rewrite Heq.
 apply Ctx_Abs.
 exact Hred.
*reflexivity.
Qed.

Lemma normalizing_app : forall (t1 t2 : Term),
  Normalizing (t1@t2) -> prod (Normalizing t1 : SProp) (Normalizing t2).
Proof.
intros t1 t2 Hnorm.
remember (t1@t2) as t' eqn:Heq.
revert t1 t2 Heq.
induction Hnorm as [ t _ IH ]; intros t1 t2 Heq.
split; apply NormalizingInd.
*intros t1' Hred.
 edestruct IH as [ Hnorm _ ].
 +rewrite Heq.
  apply Ctx_App_l.
  exact Hred.
 +reflexivity.
 +assumption.
*intros t2' Hred.
 edestruct IH as [ _ Hnorm ].
 +rewrite Heq.
  apply Ctx_App_r.
  exact Hred.
 +reflexivity.
 +assumption.
Qed.
Lemma var_normalizing : forall (n : nat), Normalizing (#n).
Proof.
intro n; apply NormalizingInd; intros t Hred; inversion Hred.
Qed.
Lemma abs_normalizing : forall (t : Term),
  Normalizing t -> Normalizing (λ t).
Proof.
intros t Hnorm.
induction Hnorm as [ t _ IH ].
apply NormalizingInd; intros t' Hred.
revert IH.
inversion_clear Hred as [ | t'' t''' Hred' | | ]; intro IH.
apply IH.
assumption.
Qed.
Lemma shift_normalizing : forall (t : Term),
  Normalizing t -> Normalizing (↑0 t).
Proof.
intros t Hnorm.
induction Hnorm as [ t _ IH ].
apply NormalizingInd.
intros t' Hred.
destruct (@shift_beta _ _ _ Hred) as [ t'' Ht'' ].
destruct Ht'' as [ Hred' Heq ].
rewrite Heq.
apply IH.
assumption.
Qed.

Lemma substitute_leaf_normalizing : forall (t : Term) (p q : nat),
  Normalizing t -> Normalizing (t[p↦#q]).
Proof.
intros t p q Hnorm.
induction Hnorm as [ t _ IH ].
apply NormalizingInd.
intros t' Hred.
destruct (@substitute_leaf_beta _ _ _ _ Hred) as [ t'' Ht'' ].
destruct Ht'' as [ Hred' Heq ].
rewrite Heq.
apply IH.
assumption.
Qed.
(** This innocent-looking lemma is essential in the λ-introduction case
  of the normalization proof *)
Lemma normalizing_substitute_leaf : forall (t : Term),
  (forall (n : nat), Normalizing (t[0↦#n])) -> Normalizing t.
Proof.
intros t Ht.
rewrite <- (@id_substitute_shift_substitute _ _ (free_var _ t) 0); [|apply le_refl].
apply substitute_leaf_normalizing.
apply shift_normalizing.
apply Ht.
Qed.
(** Definition of closure under β-reduction *)
Definition RedClosed (X : Term -> SProp) : SProp :=
  forall (t t' : Term), X t -> t ⇾ t' -> X t'.
(** A term is neutral if it is not an abstraction *)
Inductive Neutral : Term -> SProp :=
  | Var_Neutral : forall (n : nat), Neutral (#n)
  | App_Neutral : forall (t1 t2 : Term), Neutral (t1@t2).

  (** A set of terms is saturated if a neutral term is in the set
  whenever any one-step reduction of the term is in the set *)
Definition Saturated (X : Term -> SProp) :=
  forall (t : Term), Neutral t -> (forall (t' : Term), t ⇾ t' -> X t') -> X t.

  (** A reducibility candidate is a reduction-closed saturated set
  of normalizing terms *)
Definition RedCand (X : Term -> SProp) : SProp :=
  prod (forall (t : Term), X t -> Normalizing t) (prod (RedClosed X) (Saturated X)).

Lemma RedCand_Normalizing : forall (X : Term -> SProp),
  RedCand X -> forall (t : Term), X t -> Normalizing t.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Qed.
Lemma RedCand_RedClosed : forall (X : Term -> SProp), RedCand X -> RedClosed X.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Qed.
Lemma RedCand_Saturated : forall (X : Term -> SProp),
  RedCand X -> Saturated X.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Qed.
(** A reducibility candidate contains all the variables *)
Lemma RedCandVar : forall (X : Term -> SProp) (n : nat), RedCand X -> X (#n).
Proof.
intros X n Hrc.
apply RedCand_Saturated.
*assumption.
*apply Var_Neutral.
*intros t' Hred.
 inversion Hred.
Qed.
(** The set of all normalizing terms is a reducibility candidate *)
Lemma SNRedCand : RedCand Normalizing.
Proof.
split; [ | split ].
*tauto.
*intros t t' Hnorm.
 destruct Hnorm as [ IH ]; intro Hred.
 eapply IH; exact Hred.
*intros term Hneutral IH.
 apply NormalizingInd; assumption.
Qed.
(** We build the arrow of any two sets of terms *)
Definition RedCandArrow (X Y : Term -> SProp) (t1 : Term) : SProp :=
  forall (t2 : Term), X t2 -> Y (t1@t2).
(** The arrow of two reducibility candidates is a reducibility candidate *)
Lemma red_cand_arrow_RedCand : forall (X Y : Term -> SProp),
  RedCand X -> RedCand Y -> RedCand (RedCandArrow X Y).
Proof.
intros X Y Hrc1 Hrc2.
split; [ | split ].
*intros t1 Ht1.
 eapply fst; apply (@normalizing_app t1 (#0)).
 eapply RedCand_Normalizing; [ exact Hrc2 | ].
 apply Ht1.
 apply RedCand_Saturated.
 +assumption.
 +apply Var_Neutral.
 +intros t' Hred; inversion Hred.
*intros t1 t1' Ht Hred t2 Ht2.
 eapply RedCand_RedClosed; [ assumption | | apply Ctx_App_l; exact Hred ].
 apply Ht; assumption.
*intros t1 Hneutral Ht1 t2 Ht2.
 pose proof (@RedCand_Normalizing _ Hrc1 _ Ht2) as Hnorm.
 induction Hnorm as [ t2 _ IH ].
 apply RedCand_Saturated.
 +assumption.
 +apply App_Neutral.
 +intros t' Hred.
  revert Hneutral.
  inversion_clear Hred as [ t1' t2' | | t1' t1'' t2' Hred1 | t1' t2' t2'' Hred2 ]; intro Hneutral.
  -inversion Hneutral.
  -apply Ht1; assumption.
  -apply IH; [ assumption | ].
   eapply RedCand_RedClosed; [ assumption | exact Ht2 | assumption ].
Qed.
(** If [X] and [Y] are two reducibility candidates and if [t1] is a term
  such that for any [t1]∈X, [t1[0↦t2]]∈Y, then λt1∈X *)
Lemma red_cand_arrow_substitute : forall (X Y : Term -> SProp) (t1 : Term),
  RedCand X -> RedCand Y -> (forall (t2 : Term), X t2 -> Y (t1[0↦t2])) -> RedCandArrow X Y (λ t1).
Proof.
intros X Y t1 HrcX HrcY Ht1.
assert (Normalizing t1) as Hnorm1.
*apply normalizing_substitute_leaf.
 intro n.
 eapply RedCand_Normalizing.
 +exact HrcY.
 +apply Ht1.
  apply RedCandVar.
  exact HrcX.
*revert Ht1.
 induction Hnorm1 as [ t1 _ IH1 ].
 intros Ht1 t2 Ht2.
 generalize (@RedCand_Normalizing _ HrcX _ Ht2); intro Hnorm2.
 induction Hnorm2 as [ t2 _ IH2 ].
 apply RedCand_Saturated; [ assumption | apply App_Neutral | ].
 intros t' Hred.
 inversion_clear Hred as [ t1' t2' | | t1' t1'' t2' Hred1 | t1' t2' t2'' Hred2 ].
 +apply Ht1.
  assumption.
 +inversion_clear Hred1 as [ | t1''' t1'''' Hred1' | | ].
  apply IH1; [ assumption | | assumption ].
  intros t2' Ht2'.
  eapply RedCand_RedClosed.
  -assumption.
  -apply Ht1; exact Ht2'.
  -apply beta_substitute; assumption.
 +apply IH2; [ assumption | ].
  eapply RedCand_RedClosed; [ assumption | exact Ht2 | assumption ].
Qed.
(** A type context is the assignment of a set of terms for each
  type variable. If [t_ctx] is such a type context and ix [X] is
  a set of terms, then [shift_t_ctx d t_ctx X] is the type context
  obtained by assigning to n + 1 the set that was assigned to n in
  t_ctx, and assigning [X] to 0 *)
Definition shift_t_ctx (d : nat) (t_ctx : nat -> Term -> SProp) (X : Term -> SProp) : nat -> Term -> SProp :=
  fun n => match Nat.compare n d with Datatypes.Eq => X | Lt => t_ctx n | Gt => t_ctx (pred n) end.

Notation "⇧ d t" := (shift_t_ctx d t).

Lemma shift_t_ctx1 : forall (d : nat) (t_ctx : nat -> Term -> SProp) (X : Term -> SProp),
  ⇧d t_ctx X d ~ X.
Proof.
intros d t_ctx X.
unfold shift_t_ctx.
rewrite (snd (compare_eq_iff _ _)) by reflexivity.
reflexivity.
Qed.

Lemma shift_t_ctx2 : forall (d : nat) (t_ctx : nat -> Term -> SProp) (X : Term -> SProp) (n : nat),
  n >= d -> ⇧d t_ctx X (S n) ~ t_ctx n.
Proof.
intros d t_ctx X n Hge.
unfold shift_t_ctx.
rewrite nat_compare_gt.
reflexivity. now econstructor. 
Qed.
Lemma shift_t_ctx3 : forall (d : nat) (t_ctx : nat -> Term -> SProp) (X : Term -> SProp) (n : nat),
  n < d -> ⇧d t_ctx X n ~ t_ctx n.
Proof.
intros d t_ctx X n Hlt.
unfold shift_t_ctx.
rewrite nat_compare_lt; eauto.
reflexivity.
Qed.

Lemma shift_t_ctx_ext1 : forall (t_ctx : nat -> Term -> SProp) (X Y : Term -> SProp),
  (X <~> Y) -> forall (d : nat), ⇧d t_ctx X <~~> ⇧d t_ctx Y.
Proof.
simpl.
intros t_ctx X Y Heq d n term.
case (dec_le n d); intro Hdec.
*rewrite 2 shift_t_ctx3; eauto. split; auto.
* case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
 + rewrite Hdec. rewrite 2 shift_t_ctx1. apply Heq.
 + destruct n; [ inversion Hdec | ].
 eapply le_S_inv in Hdec. rewrite 2 shift_t_ctx2; eauto. split; tauto.
Qed.
Lemma shift_t_ctx_ext2 : forall (t_ctx t_ctx' : nat -> Term -> SProp) (X : Term -> SProp),
  (t_ctx <~~> t_ctx') -> forall (d : nat), ⇧d t_ctx X <~~> ⇧d t_ctx' X.
Proof.
simpl.
intros t_ctx t_ctx' X Heq d n t.
case (dec_le n d); intro Hdec.
*rewrite 2 shift_t_ctx3; eauto.
 apply Heq.
*case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
 + rewrite Hdec.
 rewrite 2 shift_t_ctx1.
 split; tauto.
 + destruct n as [ | n ]; [ inversion Hdec | ].
 eapply le_S_inv in Hdec. rewrite 2 shift_t_ctx2; eauto.
 apply Heq.
Qed.
Lemma shift_shift_t_ctx : forall (t_ctx : nat -> Term -> SProp) (X Y : Term -> SProp) (d : nat),
  ⇧0 (⇧d t_ctx X) Y <~~> ⇧(S d) (⇧0 t_ctx Y) X.
Proof.
simpl.
intros t_ctx X Y d n term.
case (dec_le n (S d)); intro Hdec.
*rewrite (@shift_t_ctx3 (S d)); auto.
 destruct n as [ | n ].
 +rewrite 2 shift_t_ctx1.
  split; tauto.
 +rewrite 2 shift_t_ctx2, shift_t_ctx3; try econstructor; try tauto.
  now eapply le_S_inv in Hdec.
* case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
 + rewrite <- Hdec.
    rewrite shift_t_ctx1, shift_t_ctx2, shift_t_ctx1; [| constructor].
 split; tauto.
 + destruct n as [ | n ]; [ inversion Hdec | ].
 eapply le_S_inv in Hdec.
 rewrite 2 shift_t_ctx2; eauto.
 destruct n as [ | n ]; [inversion Hdec |].
 eapply le_S_inv in Hdec. 
 rewrite 2 shift_t_ctx2; eauto.
 split; tauto. all: try constructor. 
Qed.
(** TypeParam is a custom type allowing notations which are specific
  to System F types *)
Inductive TypeFParam :=.
Abbreviation TypeF := (@MakeTree TypeFParam).
Notation "& n" := (@Leaf TypeFParam n).
Notation "∀ ty" := (@Bind TypeFParam ty).
Infix "⇒" := (@Node TypeFParam).
(** In a given type context, we associate to every type
  a set of terms *)
Fixpoint red_cand (t_ctx : nat -> Term -> SProp) (ty : TypeF) (t : Term) : SProp :=
  match ty with
    | Leaf n => t_ctx n t
    | Bind ty => forall (X : Term -> SProp), RedCand X -> red_cand (⇧0 t_ctx X) ty t
    | Node ty ty' => RedCandArrow (red_cand t_ctx ty) (red_cand t_ctx ty') t
  end.
Notation " t_ctx ⊩ t ∈ ty " := (red_cand t_ctx ty t).
Lemma red_cand_atom : forall (t_ctx : nat -> Term -> SProp) (n : nat), red_cand t_ctx (&n) ~ t_ctx n.
Proof.
reflexivity.
Qed.
Lemma red_cand_forall : forall (t_ctx : nat -> Term -> SProp) (ty : TypeF),
  red_cand t_ctx (∀ty) ~ fun (t : Term) => forall (X : Term -> SProp), RedCand X -> (⇧0 t_ctx X)⊩t∈ty.
Proof.
reflexivity.
Qed.
Lemma red_cand_arrow : forall (t_ctx : nat -> Term -> SProp) (ty : TypeF) (ty' : TypeF),
  red_cand t_ctx (ty⇒ty') ~ RedCandArrow (red_cand t_ctx ty) (red_cand t_ctx ty').
Proof.
reflexivity.
Qed.
Lemma red_cand_ext : forall (t_ctx t_ctx' : nat -> Term -> SProp),
  (t_ctx <~~> t_ctx') -> (forall (ty : TypeF), red_cand t_ctx ty <~> red_cand t_ctx' ty).
Proof.
simpl.
intros t_ctx t_ctx' Heq ty t.
revert t_ctx t_ctx' Heq t.
induction ty as [ m | ty IH | ty IH ty' IH' ]; intros t_ctx t_ctx' Heq t.
*rewrite 2 red_cand_atom.
 split; apply Heq.
*rewrite 2 red_cand_forall.
 split.
 +intros Ht_ctx X HrcX.
  eapply IH; [ clear IH Ht_ctx HrcX | apply Ht_ctx; exact HrcX ].
  intros n t'.
  destruct n as [ | n ].
  -rewrite 2 shift_t_ctx1.
   split; tauto.
  -rewrite 2 shift_t_ctx2; try solve [constructor].
   split; apply Heq.
 +intros Ht_ctx' X HrcX.
  eapply IH; [ clear IH Ht_ctx' HrcX | apply Ht_ctx'; exact HrcX ].
  intros n t'.
  destruct n as [ | n ].
  -rewrite 2 shift_t_ctx1.
   split; tauto.
  -rewrite 2 shift_t_ctx2; try solve [constructor].
   split; apply Heq.
*rename t into t1.
 rewrite 2 red_cand_arrow.
 split.
 +intros Ht1 t2 Ht2.
  apply (IH' t_ctx); [ split; apply Heq | ].
  apply Ht1.
  apply (IH t_ctx'); [ split; apply Heq | ].
  assumption.
 +intros Ht1 t2 Ht2.
  apply (IH' t_ctx'); [ split; apply Heq | ].
  apply Ht1.
  apply (IH t_ctx); [ split; apply Heq | ].
  assumption.
Qed.
(** If every set of terms in the type context is a reducibility
  candidate, then the set of terms associated to any type is a
  reducibility candidate *)
Lemma red_cand_RedCand : forall (t_ctx : nat -> Term -> SProp) (ty : TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> RedCand (red_cand t_ctx ty).
Proof.
intros t_ctx ty.
revert t_ctx.
induction ty as [ n | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx Ht_ctx.
*rewrite red_cand_atom.
 apply Ht_ctx.
*assert (forall (X : Term -> SProp), RedCand X -> RedCand (red_cand (⇧0 t_ctx X) ty)) as Hrc; [ | clear IH; rename Hrc into IH ].
 +intros X Hrc; apply IH.
  intro n; destruct n. 
  - rewrite shift_t_ctx1; assumption.
  - rewrite shift_t_ctx2; [|constructor]. apply Ht_ctx.
 +clear Ht_ctx.
  rewrite red_cand_forall.
  split; [ | split ].
  -intros t Ht.
   eapply RedCand_Normalizing; [ apply IH; exact SNRedCand | apply Ht; exact SNRedCand ].
  -intros t t' Ht Hred X HrcX.
   eapply RedCand_RedClosed; [ apply IH; exact HrcX | apply Ht; exact HrcX | exact Hred ].
  -intros t Hneutral Ht X HrcX.
   eapply RedCand_Saturated; [ apply IH; exact HrcX | exact Hneutral | ].
   intros t' Hred.
   apply Ht; assumption.
*rewrite red_cand_arrow.
 apply red_cand_arrow_RedCand.
 +apply IH1; assumption.
 +apply IH2; assumption.
Qed.
Lemma red_cand_shift : forall (t_ctx : nat -> Term -> SProp) (X : Term -> SProp) (ty : TypeF) (d : nat),
  red_cand t_ctx ty <~> red_cand (⇧d t_ctx X) (↑d ty).
Proof.
intros t_ctx X ty.
revert t_ctx X.
induction ty as [ n | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx X d t.
*case (dec_le n d); intro Hdec.
 +rewrite shift_leaf2, 2 red_cand_atom, shift_t_ctx3; eauto.
  split; tauto.
 + case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
  - rewrite Hdec.
  rewrite shift_leaf1, 2 red_cand_atom, shift_t_ctx2; try apply le_refl.
  split; tauto.
  - rewrite shift_leaf1, 2 red_cand_atom, shift_t_ctx2.
  split; tauto. all: eapply le_trans; eauto; apply le_S_n.
*rewrite shift_bind, 2 red_cand_forall.
 split.
 +intros Ht Y HrcY.
  apply (snd (@red_cand_ext _ _ (shift_shift_t_ctx _ _ _ _) _ _)).
  apply (fst (IH _ _ _ _)).
  apply Ht; assumption.
 +intros Ht Y HrcY.
  apply (snd (IH _ X (S d) _)).
  apply (fst (@red_cand_ext _ _ (shift_shift_t_ctx _ _ _ _) _ _)).
  apply Ht; assumption.
*rename t into t1.
 rewrite shift_node, 2 red_cand_arrow.
 split.
 +intros Ht1 t2 Ht2.
  apply IH2.
  apply Ht1.
  eapply IH1; exact Ht2.
 +intros Ht1 t2 Ht2.
  eapply IH2.
  apply Ht1.
  eapply IH1; exact Ht2.
Qed.
Lemma red_cand_shift_substitute : forall (t_ctx : nat -> Term -> SProp) (ty ty' : TypeF) (n : nat),
  red_cand (⇧n t_ctx (red_cand t_ctx ty')) ty <~> red_cand t_ctx (ty[n↦ty']).
Proof.
intros t_ctx ty; revert t_ctx.
induction ty as [ m | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx ty' n t.
*rewrite red_cand_atom.
 case (dec_le m n); intro Hdec.
 +rewrite shift_t_ctx3, substitute_leaf3, red_cand_atom; eauto.
  split; tauto.
 +case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
  - rewrite Hdec.
  rewrite shift_t_ctx1, substitute_leaf1.
  split; tauto.
  - destruct m as [ | m ]; [ inversion Hdec | ].
  rewrite shift_t_ctx2, substitute_leaf2, red_cand_atom; eauto.
  split; tauto. now eapply le_S_inv in Hdec. 
*rewrite red_cand_forall, substitute_bind, red_cand_forall.
 apply iff_forall.
 intros X HrcX.
 eapply iffE_trans; [ | apply IH ]; intro t'.
 apply red_cand_ext; clear t'.
 eapply iffE2_trans; intros n' t'; [ | apply shift_shift_t_ctx ].
 apply shift_t_ctx_ext2.
 apply shift_t_ctx_ext1.
 apply red_cand_shift.
*rewrite red_cand_arrow.
 rewrite substitute_node.
 rewrite red_cand_arrow.
 unfold RedCandArrow.
 apply iffE_forall; intro X.
 +apply IH1.
 +apply IH2.
Qed.
(** We define inductively the typing derivations of System F. Since we
  work with de Bruijn indices, a context is just a list of types, where
  the nth element is the type of the variable of index n *)

Reserved Notation " ctx ⊢ t ¦ ty ".

Inductive TermF : list TypeF -> Term -> TypeF -> SProp :=
  | VarF0 ctx ty       :    ty :: ctx ⊢ #0 ¦ ty
  | VarFS ctx ty n ty' :    ctx ⊢ #n ¦ ty' -> ty :: ctx ⊢ #(S n) ¦ ty'
  | AbsF  ctx ty t ty' :    ty :: ctx ⊢ t ¦ ty' -> ctx ⊢ λ t ¦ ty ⇒ ty'
  | AppF  ctx t ty ty' t' : ctx ⊢ t ¦ ty⇒ty' -> ctx ⊢ t' ¦ ty -> ctx ⊢ t@t' ¦ ty'
  | TAbsF ctx t ty :        ⇑ 0 ctx ⊢ t ¦ ty -> ctx ⊢ t ¦ ∀ ty
  | TAppF ctx t ty ty' :    ctx ⊢ t ¦ ∀ty  -> ctx ⊢ t ¦ ty[0↦ty']
where " ctx ⊢ t ¦ ty " := (TermF ctx t ty).

Lemma context_length : forall (ctx : list TypeF) (ty : TypeF) (n : nat),
  ctx⊢#n¦ty -> length ctx > n.
Proof.
intros ctx ty n Hderiv.
remember (#n) as t eqn:Heq.
revert n Heq.
induction Hderiv as [ ctx ty | ctx ty m ty' Hderiv IH | ctx ty t ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx  t ty Hderiv IH | ctx t ty ty' Hderiv IH ]; intros n Heq.
*injection Heq as Heq'. rewrite <- Heq'. repeat constructor.
*injection Heq as Heq'.
 generalize (IH _ refl).
 simpl. intro H. rewrite <- Heq'. now econstructor.
*discriminate.
*discriminate.
*unfold shift_list in IH. rewrite map_length in IH.
 apply IH; tauto.
*apply IH; tauto.
Qed.
Lemma free_var_context_length : forall (ctx : list TypeF) (ty : TypeF) (t : Term),
  ctx⊢t¦ty -> free_var _ t <= length ctx.
Proof.
intros ctx ty t Hderiv.
induction Hderiv as [ ctx ty | ctx ty n ty' Hderiv IH | ctx ty t1 ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx t ty Hderiv IH | ctx t ty ty' Hderiv IH ].
*rewrite free_var_leaf.
 simpl length. repeat econstructor.
*rewrite free_var_leaf in IH; rewrite free_var_leaf.
 simpl length. now constructor.
*rewrite free_var_bind.
 simpl length in IH. destruct free_var; try econstructor.
now eapply le_S_inv in IH. 
*rewrite free_var_node. now eapply max_lr.
*unfold shift_list in IH. rewrite map_length in IH; assumption.
*assumption.
Qed.
(** In a given type context, a substitution is compatible with a
  context if any element of the subtitution is in the reducibility
  candidate associated to the corresponding type in the context *)
Inductive CompatSubst : (nat -> Term -> SProp) -> list TypeF -> list Term -> SProp :=
  | CompatNil : forall (t_ctx : nat -> Term -> SProp), CompatSubst t_ctx nil nil
  | CompatCons : forall (t_ctx : nat -> Term -> SProp) (ctx : list TypeF) (s : list Term) (ty : TypeF) (t : Term), CompatSubst t_ctx ctx s -> red_cand t_ctx ty t -> CompatSubst t_ctx (ty :: ctx) (t :: s).
Lemma compat_length : forall (t_ctx : nat -> Term -> SProp) (ctx : list TypeF) (s : list Term), CompatSubst t_ctx ctx s -> length ctx ~ length s.
Proof.
intros t_ctx ctx s Hcompat.
induction Hcompat as [ | t_ctx ctx s ty t _ IH ].
*reflexivity.
*simpl; rewrite IH; reflexivity.
Qed. 
Lemma compat_id : forall (t_ctx : nat -> Term -> SProp) (ctx : list TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> CompatSubst t_ctx ctx (0…(length ctx)-1).
Proof.
intros t_ctx ctx Ht_ctx.
replace (length ctx) with (0 + length ctx)%nat; try reflexivity.
generalize 0.
induction ctx as [ | ty ctx IH ]; intro n.
*rewrite var_nil; simpl. 
 apply CompatNil. rewrite plus_zero. apply le_refl.
*rewrite var_cons; simpl.
 apply CompatCons.
 +simpl length.
  replace (n + S (length ctx))%nat with (S n + length ctx)%nat.
  apply IH. now rewrite plus_commS.
 +apply RedCandVar.
  apply red_cand_RedCand.
  assumption.
 + rewrite plus_commS. econstructor. eapply le_le. 
Qed.
(** If [t] has type [ty] in context [ctx], then for any
  type context [t_ctx] consisting of reducibility candidates,
  and for any substitution [s] compatible with [ctx] in [t_ctx],
  [t] is in the reducibility candidate associated to [ty] *)  
Lemma termf_red_cand : forall (t_ctx : nat -> Term -> SProp) (ctx : list TypeF) (s : list Term) (t : Term) (ty : TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> CompatSubst t_ctx ctx s -> ctx⊢t¦ty -> red_cand t_ctx ty (t[[0↦s]]).
Proof.
intros t_ctx ctx s t ty Ht_ctx Hcompat Hderiv.
revert t_ctx Ht_ctx s Hcompat.
induction Hderiv as [ ctx ty | ctx ty n ty' Hderiv IH | ctx ty t1 ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx t ty Hderiv IH | ctx t ty ty' Hderiv IH ]; intros t_ctx Ht_ctx s Hcompat.
*destruct s.
 +inversion Hcompat.
 +inversion_clear Hcompat.
  simpl.
  assumption.
*destruct s.
 +inversion Hcompat.
 +inversion_clear Hcompat as [ | t_ctx' ctx' s' ty'' t' Hcompat' _ ].
  specialize (IH _ Ht_ctx _ Hcompat').
  rewrite substitute_list_leaf1 in IH; [|constructor].
  rewrite minus_zero in IH.
  rewrite substitute_list_cons.
  rewrite substitute_list_leaf1; try repeat constructor.
  replace ((S n) - 1) with n; [| simpl; now rewrite minus_zero].
  erewrite nth_indep.
  -rewrite shift_list_nth.
   rewrite shift_substitute3.
   exact IH.
  -rewrite shift_list_length.
   erewrite <- compat_length; [ | exact Hcompat' ].
   eapply context_length.
   exact Hderiv.
*rewrite red_cand_arrow.
 rewrite substitute_list_bind.
 apply red_cand_arrow_substitute.
 +apply red_cand_RedCand.
  assumption.
 +apply red_cand_RedCand.
  assumption.
 +intros t2 Ht2.
  generalize (IH _ Ht_ctx (t2 :: s)); clear IH; intro IH.
  rewrite substitute_list_cons in IH.
  apply IH.
  apply CompatCons; assumption.
*specialize (IH1 _ Ht_ctx s Hcompat).
 rewrite substitute_list_node.
 rewrite red_cand_arrow in IH1.
 apply IH1.
 apply IH2; assumption.
*rewrite red_cand_forall.
 intros X HrcX.
 apply IH; clear IH t Hderiv ty.
 +intro n.
  destruct n.
  -simpl.
   assumption.
  -apply Ht_ctx.
 +revert s Hcompat.
  induction ctx as [ | ty ctx IH ]; intros s Hcompat.
  -destruct s; [ | inversion Hcompat ].
   apply CompatNil.
  -destruct s as [ | t s ]; [ inversion Hcompat | ].
   simpl.
   inversion_clear Hcompat as [ | t_ctx' ctx' s' ty' t' Hcompat' Ht' ].
   apply CompatCons; [ apply IH; assumption | clear IH Hcompat' ].
   unfold shift_t_ctx.
   unfold shift.
   apply red_cand_shift; assumption.
*specialize (IH t_ctx Ht_ctx s Hcompat).
 rewrite red_cand_forall in IH.
 specialize (IH (red_cand t_ctx ty')).
 assert (RedCand (red_cand t_ctx ty')) as Hty'.
 apply red_cand_RedCand; assumption.
 generalize (IH Hty'); clear IH Hty'.
 apply red_cand_shift_substitute.
Qed.
(** In particular, any well-typed term is normalizing *)
Lemma termf_norm : forall ctx t ty , ctx ⊢ t ¦ ty -> Normalizing t.
Proof.
intros ctx t ty Hderiv.
apply (@RedCand_Normalizing (red_cand (fun n => Normalizing) ty)).
*apply red_cand_RedCand.
 intro n; apply SNRedCand.
*rewrite <- (id_subst _ _ _ 0 (free_var_context_length _ _ _ Hderiv)).
 eapply termf_red_cand; [ | | exact Hderiv ].
 +intro n'; apply SNRedCand.
 +apply compat_id.
  intro n; apply SNRedCand.
Qed.
(** Moreover, being a normal form is a decidable property *)
Lemma normal_dec : forall (t : Term), 
sum@{SProp Type Type;_ _} (forall (t' : Term), not (t ⇾ t')) (Σ t' : Term, t ⇾ t').
Proof.
intro t; induction t as [ n | t IH | t1 IH1 t2 IH2 ].
*left.
 intros t' Hred; inversion Hred.
*destruct IH as [ IH | IH ].
 +left.
  intros t' Hred.
  inversion_clear Hred as [ | t'' t''' Hred' | | ].
  eapply IH; exact Hred'.
 +right.
  destruct IH as [ t' IH ].
  exists (λ t').
  apply Ctx_Abs; assumption.
*destruct IH1 as [ IH1 | [ t1' IH1] ]; [ | right; exists (t1'@t2); apply Ctx_App_l; assumption ].
 destruct IH2 as [ IH2 | [ t2' IH2 ] ]; [ | right; exists (t1@t2'); apply Ctx_App_r; assumption ].
 destruct t1 as [ n | t1 | t11 t12 ].
 +left.
  intros t' Hred.
  inversion_clear Hred as [ | | t1 t1' t2' Hred1 | t1 t2' t2'' Hred2 ]; [ inversion Hred1 | ].
  eapply IH2; exact Hred2.
 +right.
  exists (t1[0↦t2]).
  apply Beta.
 +left.
  intros t' Hred.
  inversion_clear Hred as [ | | t1' t1'' t2' Hred1 | t1' t2' t2'' Hred2 ].
  -eapply IH1; exact Hred1.
  -eapply IH2; exact Hred2.
Defined.
(** Therefore we can compute the normal form of any normalizing term *)
Lemma normal_form : forall (t : Term), Normalizing t -> Σ t' : Term, t ⇾* t' /\ forall t'', not (t' ⇾ t'').
Proof.
intros t Hnorm.
unshelve eapply (@Normalizing_rec t (fun t => Σ t' : Term, t ⇾* t' /\ (forall t'' : Term, not (t' ⇾ t''))) _ Hnorm). 
intros t0 X. simpl.
case (normal_dec t0); intro Hdec.
*exists t0.
 split.
 +apply Refl.
 +assumption.
*destruct Hdec as [t' Hred ].
 destruct (X _ Hred) as [ t'' IH' ]; clear X.
 destruct IH' as [ Hred' Hnorm' ].
 exists t''.
 split.
 +eapply Trans.
  -exact Hred.
  -assumption.
 +assumption.
Defined.
(** So in particular we can compute the normal form of any term
  which is well-typed in System F *)
Lemma termf_normal_form : forall (ctx : list TypeF) (t : Term) (ty : TypeF),
  TermF ctx t ty -> Σ t' : Term, t ⇾* t' /\ forall t'', not (t' ⇾ t'').
Proof.
intros ctx t ty Hderiv.
apply normal_form.
eapply termf_norm; exact Hderiv.
Defined.

Definition nf (ctx : list TypeF) (t : Term) (ty : TypeF) (p : ctx ⊢ t ¦ ty) : Term
  := match termf_normal_form _ _ _ p with exist u _ => u end.

Ltac auto_typing := repeat (econstructor; cbn).

Lemma omegaTypeF Γ : Γ ⊢ λ (#0@#0) ¦ ∀(&0⇒&0) ⇒ ∀(&0⇒&0).
Proof.
auto_typing.
change (∀(&0⇒&0)⇒∀(&0⇒&0)) with ((&0⇒&0)[0↦∀(&0⇒&0)]).
auto_typing.
Qed.

Definition church_nat := ∀ (&0 ⇒ (&0⇒&0) ⇒ &0).

Definition zero := λ λ #1.

Lemma zeroT Γ : Γ ⊢ zero ¦ church_nat.
Proof.
auto_typing.
Qed.
  
Definition succ := λ λ λ #0 @ (#2 @ #1 @ #0).

Lemma succT Γ : Γ ⊢ succ ¦ church_nat ⇒ church_nat.
Proof.
auto_typing.
change ((&0⇒(&0⇒&0)⇒&0)) with ((&0⇒(&0⇒&0)⇒&0)[0↦&0]).
auto_typing.
Qed.

Definition one := λ λ (# 0 @ # 1).

Lemma oneT Γ : Γ ⊢ one ¦ church_nat.
Proof.
auto_typing.
Qed.

Definition two := λ λ (# 0 @ (# 0 @ # 1)).

Definition three := succ @ two.

Definition plus := λ (*n*) λ (*m*) (#1 @ #0 @ succ).

Lemma plusT Γ : Γ ⊢ plus ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 3 econstructor.
  2: apply succT.
  auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Qed. 

Definition mult := λ (*n*) λ (*m*) (#1 @ zero @ (plus @ #0)).

Lemma multT Γ : Γ ⊢ mult ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 4 econstructor.
  3: apply plusT.
  2: apply zeroT. 
  all: auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Qed. 

Definition exp := λ (*n*) λ (*m*) (#0 @ one @ (mult @ #1)).

Lemma expT Γ : Γ ⊢ exp ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 4 econstructor.
  2: apply oneT. 
  2: apply multT.
  all: auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Qed. 

Definition four := mult @ two @ two.

Definition exp2 n := exp @ two @ n.

Ltac auto_typing_nat := abstract (repeat (first [apply succT | apply plusT | apply multT | apply expT | econstructor]; cbn)).

From Ltac2 Require Import Ltac2.

From Ltac2 Require Import Message.

From Ltac2 Require Import Ref.

Lemma Norm_unfold : forall P p t q, Normalizing_rec t P p q ~ p t (fun y r => Normalizing_rec y P p (normInv t q y r)).
Proof.
  now intros; unfold Normalizing_rec; rewrite Acc_el_comp.
Qed. 


Definition tm_id := (λ (# 0)).

Definition example : Term := tm_id @ (# 0).

Ltac2 Notation "auto_Norm_unfold" := let n := ref 0 in 
    repeat (incr n; rewrite Norm_unfold; lazy);
    print (concat (of_string "number of reduction steps: ")
                  (of_int (get n))).

(* Let's play with the Church encoding of natural numbers *)

Fail Check obseq_refl : nf nil (succ @ zero) church_nat ltac:(auto_typing_nat) ~ one.

Goal nf nil (exp2 two) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ exp2 one @ exp2 one) church_nat ltac:(auto_typing_nat).
  unfold exp2, four, two, three, mult, plus, exp, succ, two, zero.
  unfold nf, termf_normal_form, normal_form.
  print (of_string "prop scenario: exp 2 2 = exp 2 1 + exp 2 1").
  Time auto_Norm_unfold.
  reflexivity.
Abort.

Goal nf nil (exp2 three) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ exp2 two @ exp2 two) church_nat ltac:(auto_typing_nat).
  unfold exp2, four, two, three, mult, plus, exp, succ, two, zero.
  unfold nf, termf_normal_form, normal_form.
  print (of_string "prop scenario: exp 2 3 = exp 2 2 + exp 2 2").
  print (of_string "** Uncomment in the file if you want to see the result **").
(*  Time auto_Norm_unfold. 
  reflexivity. *)
Abort. 

Goal nf nil (exp2 four) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ exp2 three @ exp2 three) church_nat ltac:(auto_typing_nat).
  unfold exp2, four, two, three, mult, plus, exp, succ, two, zero, one.
  unfold nf, termf_normal_form, normal_form.
  print (of_string "prop scenario: exp 2 4 = exp 2 3 + exp 2 3").
  print (of_string "** Uncomment in the file if you want to see the result **").
(*  Time auto_Norm_unfold.
  reflexivity.*)
Abort. 


(* Let's play with the Church encoding of natural numbers *)

#[rewrite_rules(Acc_el_def)]
Goal nf nil (exp2 two) church_nat ltac:(auto_typing_nat) ~
     nf nil (plus @ exp2 one @ exp2 one) church_nat ltac:(auto_typing_nat).
Proof. 
  print (of_string "def scenario: exp 2 2 = exp 2 1 + exp 2 1").
  Time lazy; reflexivity.
Abort.

#[rewrite_rules(Acc_el_def)]
Goal nf nil (exp2 three) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ exp2 two @ exp2 two) church_nat ltac:(auto_typing_nat).
  print (of_string "def scenario: exp 2 3 = exp 2 2 + exp 2 2").
  Time lazy; reflexivity.
Abort.

#[rewrite_rules(Acc_el_def)]
Goal nf nil (exp2 four) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ (exp2 three) @ (exp @ two @ three)) church_nat ltac:(auto_typing_nat).
  print (of_string "def scenario: exp 2 4 = exp 2 3 + exp 2 3").
  Time lazy. reflexivity.
Abort.

Definition five := plus @ four @ one.
Definition six := plus @ five @ one.
Definition seven := plus @ four @ three.
Definition eight := exp @ two @ three.
Definition nine := plus @ eight @ one.
Definition ten := plus @ nine @ one.

#[rewrite_rules(Acc_el_def)]
Goal nf nil (exp2 eight) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ (exp @ two @ seven) @ (exp @ two @ seven)) church_nat ltac:(auto_typing_nat).
  print (of_string "def scenario: exp 2 8 = exp 2 7 + exp 2 7").
  Time lazy; reflexivity.
Abort. 

#[rewrite_rules(Acc_el_def)]
Goal nf nil (exp @ two @ nine) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ (exp @ two @ eight) @ (exp @ two @ eight)) church_nat ltac:(auto_typing_nat).
  print (of_string "def scenario: exp 2 9 = exp 2 8 + exp 2 8").
  Time lazy; reflexivity.
Abort. 
(*
Goal nf nil (exp @ two @ ten) church_nat ltac:(auto_typing_nat) ~ 
     nf nil (plus @ (exp @ two @ nine) @ (exp @ two @ nine)) church_nat ltac:(auto_typing_nat).
  print (of_string "def scenario: exp 2 10 = exp 2 9 + exp 2 9").
  Time lazy; reflexivity.
Abort. 
*)
