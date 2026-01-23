Set Universe Polymorphism.

Open Scope type_scope.

From SystemF Require Import Sigma sum Observational Arith List.

Reserved Notation "↑ d t" (at level 27, d at level 0, t at level 0).
Reserved Notation "t [ n ↦ u ]" (at level 26, left associativity).
Reserved Notation "⇑ d t" (at level 27, d at level 0, t at level 0).
Reserved Notation "t [[ n ↦ s ]]" (at level 26, left associativity).
Reserved Notation "⇧ d t" (at level 10, d at level 0, t at level 0).
Reserved Notation "# n" (at level 25, n at level 0).
Reserved Notation "'λ' t" (at level 28, t at level 0).
Reserved Notation "t1 @ t2" (at level 29, left associativity).
Reserved Notation "& n" (at level 25).
Reserved Notation "∀ ty" (at level 28).
Reserved Notation "ty1 ⇒ ty2" (at level 30, right associativity).
Reserved Notation "t ⇾ t'" (at level 70, no associativity).
Reserved Notation "t ⇾* t'" (at level 70, no associativity).
Reserved Notation "t ⇾' t'" (at level 70, no associativity).
Reserved Notation "t ⇾'* t'" (at level 70, no associativity).
Reserved Notation "t ⇾₀ t'" (at level 70, no associativity).
Reserved Notation "t ⇾₀* t'" (at level 70, no associativity).
Reserved Notation " t_ctx ⊩ term ∈ type " (at level 70, no associativity).
Reserved Notation " ctx ⊢ term ¦ type " (at level 70, no associativity).
Reserved Notation "p … n -1" (at level 30, no associativity).

Section Substitutions.
(** * Binary trees

  This section contains all the technical stuff about
  binary trees with binders (encoded using de Bruijn indices).
  These trees will be used for pure λ-terms as well as for
  System F types
  ----In this definition, the [A] parameter is only a trick allowing
  to have different notations for λ-terms and System F types *)
Inductive MakeTree {A : Type} : Type :=
  | Leaf : nat -> @MakeTree A
  | Bind : @MakeTree A -> @MakeTree A
  | Node : @MakeTree A -> @MakeTree A -> @MakeTree A.
Variable A : Type.
Abbreviation Tree := (@MakeTree A).
Notation "# n" := (@Leaf A n).
Notation "'λ' t" := (@Bind A t).
Infix "@" := (@Node A).

(** [shift d t] increases every free variable of [t] which has an
  index >= [d]. This will be used in the definition of substitution *)
Fixpoint shift (depth : nat) (tree : Tree) : Tree :=
  match tree with
    | Leaf n => if depth <=? n then #(S n) else #n
    | Bind t => λ(shift (S depth) t)
    | Node t1 t2 => (shift depth t1)@(shift depth t2)
  end.
Notation "↑ d t" := (shift d t).

Lemma shift_leaf1 : forall (d n : nat),
  n >= d -> ↑d(#n) ~ #(S n).
Proof.
intros d n Hge0.
unfold shift.
rewrite leb_correct; try reflexivity; eauto.
Qed.

Lemma shift_leaf2 : forall (d n : nat),
  n < d -> ↑d(#n) ~ #n.
Proof.
intros d n Hlt.
unfold shift.
rewrite leb_correct_conv; try reflexivity; eauto.
Qed.
Lemma shift_bind : forall (d : nat) (t : Tree),
  ↑d(λ t) ~ λ(↑(S d) t).
Proof.
reflexivity.
Qed.
Lemma shift_node : forall (d : nat) (t t' : Tree),
  ↑d(t@t') ~ (↑d t)@(↑d t').
Proof.
reflexivity.
Qed.

Lemma shift_shift : forall (d d' : nat) (t : Tree),
  d' <= d -> ↑d'(↑d t) ~ ↑(S d)(↑d' t).
Proof.
intros d d' t.
revert d d'.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intros d d' Hle.
* case (le_dec d n); intro Hdec.
  + rewrite 4 shift_leaf1; try now constructor.
    - eapply le_trans; eauto.
    - eapply le_trans; eauto.
      eapply le_trans; try apply le_S_n. now constructor.
    - eauto. 
 + case (le_dec d' n); intro Hdec'.
  - rewrite shift_leaf2.
    rewrite shift_leaf1.
    rewrite shift_leaf2.
    reflexivity.
    ++ econstructor. now eapply not_le_lt in Hdec.
    ++ eauto.
    ++ now eapply not_le_lt in Hdec.
  - rewrite 3 shift_leaf2.
    reflexivity.
    ++ constructor. eapply not_le_lt in Hdec.
       eapply le_trans. apply le_S_n. eauto. 
    ++ now eapply not_le_lt in Hdec'.
    ++ now eapply not_le_lt in Hdec.
* rewrite 4 shift_bind. apply ap.
 rewrite IH; now constructor.
* rewrite 4 shift_node.
  rewrite IH1; eauto.
  apply ap. apply IH2; eauto.
Qed.


(** [substitute n t t'] substitutes [t'] for the free variable of
  index [n] in [t], and decreases all the free variables of [t]
  which have an index > [n] *)
Fixpoint substitute (n : nat) (tree tree' : Tree) : Tree :=
  match tree with
    | Leaf m => match m ?= n with Datatypes.Eq => tree' | Lt => #m | Gt => #(pred m) end
    | Bind t => λ(substitute (S n) t (↑0 tree'))
    | Node t1 t2 => (substitute n t1 tree')@(substitute n t2 tree')
  end.
Notation "t [ n ↦ u ]" := (substitute n t u).
Lemma substitute_leaf1 : forall (n : nat) (t : Tree),
  #n[n↦t] ~ t.
Proof.
intros n t.
unfold substitute.
rewrite (snd (compare_eq_iff _ _)) by reflexivity.
reflexivity.
Qed.

Lemma substitute_leaf2 : forall (n m : nat) (t : Tree),
  n < m -> #m[n↦t] ~ #(pred m).
Proof.
intros n m t Hgt.
unfold substitute.
rewrite (nat_compare_gt _ _); eauto.
reflexivity.
Qed.

Definition nat_compare_lt n m : (n < m) -> (n ?= m) ~ Lt.
  revert m; induction n; cbn; intros.
  - now inversion H.  
  - destruct m; try reflexivity.
    + inversion H.
    + eapply IHn. now inversion H.
Qed.

Lemma substitute_leaf3 : forall (n m : nat) (t : Tree),
  m < n -> #m[n↦t] ~ #m.
Proof.
intros n m t Hgt.
unfold substitute.
rewrite (nat_compare_lt _ _); eauto.
reflexivity.
Qed.

Lemma substitute_bind : forall (n : nat) (t t' : Tree),
  (λ t)[n↦t'] ~ λ(t[S n↦↑0 t']).
Proof.
reflexivity.
Qed.

Lemma substitute_node : forall (n : nat) (t1 t2 t' : Tree),
  (t1@t2)[n↦t'] ~ t1[n↦t']@t2[n↦t'].
Proof.
reflexivity.
Qed.

Lemma shift_substitute1 : forall (n d : nat) (t t' : Tree),
  d <= n -> (↑d t)[S n↦↑d t'] ~ ↑d (t[n↦t']).
Proof.
intros n d t t'.
revert n d t'.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n d t' Hle.
* case (dec_le n m); intro Hdec.
 + rewrite shift_leaf1, 2 substitute_leaf2, shift_leaf1.
  apply ap. cbn. destruct m; [inversion Hdec|]; simpl; eauto.
  now apply ap. destruct m; [inversion Hdec|]; simpl.
  eapply le_S_inv in Hdec. eapply le_trans; eauto.
  eauto. now econstructor. eapply le_trans; eauto.
  eapply le_trans; try apply le_S_n. eauto.
 + case (le_compare_dec _ _ Hdec); clear Hdec.
  ++ intros Hdec; rewrite Hdec.
  rewrite shift_leaf1, 2 substitute_leaf1.
  reflexivity. eauto.
  ++ intro Hdec.  case (le_dec d m); intro Hdec'.
  - rewrite substitute_leaf3, shift_leaf1, substitute_leaf3.
   reflexivity. 
   ** now constructor.
   ** eauto. 
   ** eauto. 
  -rewrite substitute_leaf3, shift_leaf2, substitute_leaf3.
   reflexivity.
   ** econstructor. eapply le_trans; try apply le_S_n. eauto.
   ** now eapply not_le_lt in Hdec'.
   ** eauto.
*rewrite shift_bind, 2 substitute_bind, shift_bind. apply ap.
 rewrite shift_shift.
 rewrite IH. 
 reflexivity.
 + now constructor.
 + constructor.   
*rewrite shift_node, 2 substitute_node, shift_node. 
  rewrite IH1; eauto.  apply ap.
  apply IH2; eauto.
Qed.

Lemma shift_substitute2 : forall (n d : nat) (t t' : Tree),
  d >= n -> (↑(S d) t)[n↦↑d t'] ~ ↑d(t[n↦t']).
Proof.
intros n d t t'.
revert n d t'.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n d t' Hle.
* case (dec_le n m); intro Hdec.
 + case (le_dec (S d) m); intro Hdec'.
  - rewrite substitute_leaf2, shift_leaf1, substitute_leaf2, shift_leaf1; eauto.
    apply ap. 
    destruct m; try reflexivity. inversion Hdec'.
    destruct m; cbn. inversion Hdec'. now eapply le_S_inv in Hdec'. 
    eapply le_lt_trans; eauto. eapply le_S_n.
  - rewrite substitute_leaf2, shift_leaf2, substitute_leaf2, shift_leaf2; eauto.
    reflexivity.
    destruct m; cbn. inversion Hdec.
    eapply not_le_lt in Hdec'. now eapply le_S_inv in Hdec'. 
    econstructor. eapply not_le_lt in Hdec'. now eapply le_S_inv in Hdec'. 
  + case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec. 
  ++ rewrite Hdec.
   rewrite shift_leaf2, 2 substitute_leaf1.
   reflexivity. now econstructor.
  ++ rewrite shift_leaf2, 2 substitute_leaf3, shift_leaf2; eauto. 
   reflexivity. 
   eapply le_lt_trans; eauto. 
   econstructor. eapply le_trans; eauto. eapply le_trans; try apply le_S_n; eauto. 
* rewrite shift_bind, 2 substitute_bind, shift_bind. apply ap.
  rewrite shift_shift; eauto.
  rewrite IH; try reflexivity.
  all :now econstructor.
* rewrite shift_node, 2 substitute_node, shift_node. 
  rewrite IH1; eauto. apply ap. apply IH2; eauto.
Qed.

Lemma shift_substitute3 : forall (d : nat) (t t' : Tree),
  (↑d t)[d↦t'] ~ t.
Proof.
intros d t.
revert d.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intros d t'.
*case (le_dec d n); intro Hdec.
 + rewrite shift_leaf1; eauto.
   rewrite substitute_leaf2. reflexivity. now econstructor.
 + eapply not_le_lt in Hdec. 
   rewrite shift_leaf2, substitute_leaf3; eauto.
   reflexivity.
* now rewrite shift_bind, substitute_bind, IH.
* now rewrite shift_node, substitute_node, IH1, IH2.
Qed.
Lemma substitute_substitute : forall (n n' : nat) (t t' t'' : Tree),
  n <= n' -> t[n↦t'][n'↦t''] ~ t[S n'↦↑n t''][n↦t'[n'↦t''] ].
Proof.
intros n n' t t' t'' Hle.
revert n n' Hle t' t''.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n n' Hle t' t''.
* case (dec_le n m); intro Hdec.
 + case (dec_le (S n') m); intro Hdec'.
  - rewrite 4 substitute_leaf2; eauto.
    reflexivity. 
    ++ destruct m; simpl. inversion Hdec. eapply le_S_inv in Hdec'.
       eapply lt_le_trans; eauto.
    ++ destruct m; simpl. inversion Hdec. eapply le_S_inv in Hdec'.
       eapply lt_le_trans; eauto. eapply le_refl.
  - case (le_compare_dec _ _ Hdec'); clear Hdec'; intro Hdec'.
   ++ rewrite <- Hdec'.
   rewrite substitute_leaf2; eauto. 
   rewrite substitute_leaf1. rewrite Hdec'. unfold Nat.pred.
   rewrite substitute_leaf1. rewrite shift_substitute3; eauto.
   reflexivity.
   ++ rewrite substitute_leaf2, 2 substitute_leaf3, substitute_leaf2; eauto.
   reflexivity. destruct m; simpl. inversion Hdec. now eapply le_S_inv in Hdec'.
 + case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
  - rewrite Hdec.
    rewrite substitute_leaf1, substitute_leaf3, substitute_leaf1.
    reflexivity. now econstructor.
  - rewrite 4 substitute_leaf3; eauto.
    reflexivity. 
    eapply le_lt_trans; eauto. eapply le_trans; eauto. apply le_S_n.
    eapply le_lt_trans; eauto.
* rewrite 4 substitute_bind. apply ap.
  rewrite IH.
  rewrite shift_substitute1, <- shift_shift; try econstructor.
  now econstructor.
* rewrite 4 substitute_node. rewrite IH1; eauto.
  apply ap, IH2; eauto. 
Qed.

(** [free_var t] picks the least index n such that every free variable
  appearing in [t] has index < n *)
Fixpoint free_var (tree : Tree) :=
  match tree with
    | Leaf n => S n
    | Bind t => pred (free_var t)
    | Node t1 t2 => max (free_var t1) (free_var t2)
  end.
Lemma free_var_leaf : forall (n : nat), free_var (#n) ~ S n.
Proof.
intro n.
reflexivity.
Qed.
Lemma free_var_bind : forall (t : Tree),
  free_var (λ t) ~ pred (free_var t).
Proof.
intro t.
reflexivity.
Qed.
Lemma free_var_node : forall (t1 t2 : Tree),
  free_var (t1@t2) ~ max (free_var t1) (free_var t2).
Proof.
intros t1 t2.
reflexivity.
Qed.

Lemma shift_free_var : forall (t : Tree) (d : nat),
  d >= free_var t -> ↑d t ~ t.
Proof.
intro t.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intro d.
*rewrite free_var_leaf; intro Hge.
 rewrite shift_leaf2; eauto.
 reflexivity.
*rewrite free_var_bind; intro Hge.
 rewrite shift_bind, IH.
 reflexivity. destruct free_var; now econstructor.
*rewrite free_var_node; intro Hge.
 rewrite shift_node, IH1.
 apply ap. apply IH2.
 eapply le_trans; try apply max_r; eauto.
 eapply le_trans; try apply max_l; eauto.
Qed.

Lemma substitute_free_var : forall (t : Tree) (n : nat) (t' : Tree),
  n >= free_var t -> t[n↦t'] ~ t.
intro t.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n t'.
* rewrite free_var_leaf; intro Hge.
  rewrite substitute_leaf3; eauto.
  reflexivity.
* rewrite free_var_bind; intro Hge.
  rewrite substitute_bind, IH.
  reflexivity. destruct free_var; now econstructor.
* rewrite free_var_node; intro Hge.
  rewrite substitute_node, IH1.
  apply ap. apply IH2. 
  eapply le_trans; try apply max_r; eauto.
  eapply le_trans; try apply max_l; eauto.
Qed.

(** This lemma states that the substitution of a big enough variable
  for any given variable can be reverted *)
Lemma id_substitute_shift_substitute : forall (t : Tree) (n p : nat),
  n >= free_var t -> (↑p (t[p↦#n]))[S n↦#p] ~ t.
Proof.
intro t; induction t as [ q | t IH | t1 IH1 t2 IH2 ]; intros n p.
* rewrite free_var_leaf; intro Hge.
  case (dec_le p q); intro Hdec.
 +rewrite substitute_leaf2, shift_leaf1, substitute_leaf3; eauto.
   apply ap. 
   destruct q; now inversion Hdec.
   destruct q; simpl. inversion Hdec. econstructor. 
   eapply lt_le_trans; eauto. eapply le_S_n.
   destruct q; now inversion Hdec.
 + case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec.
  - rewrite Hdec.
  rewrite substitute_leaf1, shift_leaf1, substitute_leaf1; eauto.
  reflexivity. rewrite <- Hdec. eapply le_trans; try apply le_S_n; eauto. 
  - rewrite substitute_leaf3, shift_leaf2, substitute_leaf3; eauto.
  reflexivity. eapply le_lt_trans; try apply Hge. eapply le_S_n. 
*rewrite free_var_bind; intro Hge.
 rewrite substitute_bind, shift_bind, substitute_bind. apply ap.
 rewrite 2 shift_leaf1; try econstructor.
 apply IH. destruct free_var; now econstructor.
*rewrite free_var_node; intro Hge.
 rewrite substitute_node, shift_node, substitute_node. 
 rewrite IH1, IH2. reflexivity.
 eapply le_trans; try apply max_r; eauto.
 eapply le_trans; try apply max_l; eauto.
Qed.
(** [shift_list d s] performs [shift d t] for every [t] of [s].
  This will be used in the definition of parallel substitution *)
Definition shift_list (depth : nat) (trees : list Tree) : list Tree :=
  map (fun tree : Tree => ↑depth tree) trees.
Notation "⇑ d t" := (shift_list d t).
Lemma shift_list_nil : forall (d : nat), ⇑d nil ~ nil.
Proof.
intro d.
unfold shift_list.
reflexivity.
Qed.
Lemma shift_list_cons : forall (d : nat) (t : Tree) (trees : list Tree),
  ⇑d (t::trees) ~ (↑d t :: ⇑d trees).
Proof.
intro d.
unfold shift_list.
reflexivity.
Qed.
Lemma shift_list_length : forall (d : nat) (trees : list Tree),
  length (⇑d trees) ~ length trees.
Proof.
intros d trees.
unfold shift_list.
apply map_length.
Qed.
Lemma shift_list_nth : forall (d : nat) (trees : list Tree) (n : nat) (t : Tree),
  nth n (⇑d trees) (↑d t) ~ ↑d (nth n trees t).
Proof.
intros d trees n t.
unfold shift_list.
apply map_nth.
Qed.
Lemma shift_list_shift_list : forall (d d' : nat) (trees : list Tree),
  d' <= d -> ⇑d'(⇑d trees) ~ ⇑(S d)(⇑d' trees).
Proof.
intros d d' trees Hle.
induction trees as [ | t trees IH ].
*rewrite 2 shift_list_nil.
 reflexivity.
*rewrite 4 shift_list_cons, shift_shift; eauto.
 rewrite IH.
 reflexivity.
Qed.
(** [substitute_list n t s] performs parallel substitution of the
  [m]th element of [s] for the free variable of index [n + m] in [t],
  and subtracts [length s] to all the free variables of [t]
  which have an index >= [n + length s] *)
Fixpoint substitute_list (n : nat) (tree : Tree) (subst : list Tree) : Tree :=
  match tree with
    | Leaf m => if n <=? m then nth (m - n) subst (#(m - (length subst))) else #m
    | Bind t => λ (substitute_list (S n) t (⇑0 subst))
    | Node t1 t2 => (substitute_list n t1 subst)@(substitute_list n t2 subst)
  end.
Notation " t [[ n ↦ s ]]" := (substitute_list n t s).
Lemma substitute_list_leaf1 : forall (n m : nat) (s : list Tree),
  m >= n -> #m[[n↦s]] ~ nth (m - n) s (#(m - length s)).
Proof.
intros n m s Hge.
unfold substitute_list.
rewrite leb_correct; eauto. 
reflexivity.
Qed.
Lemma substitute_list_leaf2 : forall (n m : nat) (s : list Tree),
  m < n -> #m[[n↦s]] ~ #m.
Proof.
intros n m s Hge.
unfold substitute_list.
rewrite leb_correct_conv; eauto.
reflexivity.
Qed.
Lemma substitute_list_bind : forall (n : nat) (t : Tree) (s : list Tree),
  (λ t)[[n↦s]] ~ λ (t[[S n↦⇑0 s]]).
Proof.
intros n t s.
reflexivity.
Qed.
Lemma substitute_list_node : forall (n : nat) (t1 t2 : Tree) (s : list Tree),
  (t1@t2)[[n↦s]] ~ t1[[n↦s]]@t2[[n↦s]].
Proof.
intros n t1 t2 s.
reflexivity.
Qed.
Lemma substitute_list_nil : forall (n : nat) (t : Tree), t[[n↦nil]] ~ t.
Proof.
intros n t; revert n.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intro n.
* case (le_dec n m); intro Hdec.
 +rewrite substitute_list_leaf1; eauto.
  rewrite nth_overflow. apply ap; simpl.
  apply minus_zero. econstructor.
 +rewrite substitute_list_leaf2.
  reflexivity. now eapply not_le_lt.
* rewrite substitute_list_bind. apply ap.
  now rewrite IH.
* rewrite substitute_list_node. 
  now rewrite IH1, IH2.
Qed.

Lemma substitute_list_cons : forall (n : nat) (t : Tree) (s : list Tree) (t' : Tree),
  t[[n↦t'::s]] ~ t[[S n↦⇑n s]][n↦t'].
Proof.
intros n t; revert n.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n s t'.
* case (dec_le n m); intro Hdec.
 +rewrite 2 substitute_list_leaf1, shift_list_length; eauto.
  2: { eapply le_trans; eauto. apply le_S_n. }
  destruct m as [ | m ]; [ inversion Hdec | ].
  replace (S m - n) with (S (m - n)).
  2: { destruct n; simpl. now rewrite minus_zero. eapply le_S_inv in Hdec.
      now rewrite minus_S. }
  simpl nth at 1.
  change (S m - S n) with (m - n).
  rewrite <- (shift_substitute3 n _ t'). 
  rewrite <- shift_list_nth.
  apply (ap _ _ (fun x => x [n ↦ t'])). 
  case (dec_le (m - n) (length s)); intro Hdec'.
  - eapply nth_indep.
   rewrite shift_list_length; eauto.
  - apply ap. rewrite shift_leaf1. apply ap.
    destruct length; simpl. 
    now rewrite minus_zero.
    rewrite minus_S. reflexivity. 
    eapply le_lt_trans; eauto. apply minus_less.
    eapply minus_plus_le. rewrite plus_comm.
    eapply le_S_inv in Hdec.  now eapply minus_plus_le'.
 +case (le_compare_dec _ _ Hdec); clear Hdec; intro Hdec. 
  ++ rewrite <- Hdec.
  rewrite substitute_list_leaf1, substitute_list_leaf2, substitute_leaf1.
  replace (m - m) with 0 by now rewrite minus_refl. simpl nth.
  reflexivity. all: apply le_refl. 
  ++ rewrite 2 substitute_list_leaf2, substitute_leaf3; eauto.
  reflexivity. eapply le_lt_trans; eauto. apply le_S_n. 
*rewrite 2 substitute_list_bind, substitute_bind, shift_list_cons, shift_list_shift_list; [| constructor].
 apply ap, IH.
* rewrite 2 substitute_list_node, substitute_node.
  rewrite IH1, IH2. reflexivity.
Qed.
(** [var_seq p n] is the list of variables of index  [p] to [n-1] *)
Definition var_seq (p n : nat) : list Tree :=
  map (fun n => #n) (seq p (n - p)).
Notation "p … n -1" := (var_seq p n).
Lemma var_nil : forall (p n : nat), p >= n -> (p…n-1) ~ nil.
Proof.
intros n p Hle.
unfold var_seq.
replace (p - n) with 0.
reflexivity. apply minus_le in Hle. now rewrite Hle.
Qed.


Lemma var_cons : forall (p n : nat),
  p < n -> (p…n-1) ~ (#p::((S p)…n-1)).
Proof.
intros n p Hle.
unfold var_seq.
destruct p as [ | p ]; [ inversion Hle | ].
replace (S p - n) with (S (p - n)).
reflexivity. eapply le_S_inv in Hle. now apply minus_S_le. 
Qed.
Lemma var_nth : forall (p n m : nat) (t : Tree),
  m < n - p -> nth m (p…n-1) t ~ #(p + m).
Proof.
intros p n m t Hineq.
unfold var_seq.
rewrite (nth_indep _ _ _ (#0)).
*rewrite map_nth, seq_nth; eauto. reflexivity.
* rewrite map_length, seq_length; eauto.
Qed.
Lemma var_shift : forall (p n d : nat),
  d <= p -> ⇑d(p…n-1) ~ (S p)…(S n)-1.
Proof.
intros p n d Hle.
unfold var_seq.
unfold shift_list.
rewrite map_map, <- seq_shift, map_map.
replace (S n - S p) with (n - p); try reflexivity.
generalize (n - p); clear n; intro n.
revert p d Hle.
induction n as [ | n IH ]; intros p d Hle.
*reflexivity.
*simpl seq.
 simpl map.
 rewrite leb_correct; eauto. apply ap.
 rewrite <- (IH _ d).
 apply map_ext.
 reflexivity. eapply le_trans; eauto. apply le_S_n.
Qed.

Lemma id_subst : forall (t : Tree) (n p : nat),
  n >= free_var t -> t[[p↦p…n-1]] ~ t.
Proof.
intro t.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n p.
*rewrite free_var_leaf.
 case (le_dec p m); intros Hdec Hle.
 +rewrite substitute_list_leaf1; eauto.
  rewrite var_nth. apply ap. now eapply minus_plus.
  now eapply lt_to_minus'.
 +rewrite substitute_list_leaf2.
  reflexivity. now eapply not_le_lt.
*rewrite free_var_bind; intro Hge.
 rewrite substitute_list_bind, var_shift; try econstructor.
 rewrite IH.
 reflexivity. destruct free_var; now econstructor.
*rewrite free_var_node; intro Hge.
 rewrite substitute_list_node.
 rewrite IH1, IH2. reflexivity.
 eapply le_trans; try apply max_r; eauto.
 eapply le_trans; try apply max_l; eauto.
Qed.
End Substitutions.