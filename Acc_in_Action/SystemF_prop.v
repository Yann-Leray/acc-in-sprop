(* adapted from a proof by Valentin Blot *)

Set Warnings "-level-tolerance".
Set Universe Polymorphism.

From Stdlib Require Import Arith.
Require Import ComputeEq.

#[global]
Instance iff_flip_impl_subrelation : RelationClasses.subrelation iff (CRelationClasses.flip Basics.impl) | 2.
Proof. firstorder. Defined.

Fixpoint map {A B} (f : A -> B) (l:list A) : list B :=
  match l with
    | nil => nil
    | cons a l => cons (f a) (map f l)
  end.

Lemma map_length {A' B'} (f : A' -> B') : forall l, length (map f l) = length l.
  induction l; cbn. 
  - reflexivity.
  - f_equal; eauto.
Defined.

Infix "::" := cons (at level 60, right associativity).

Fixpoint nth {B} (n:nat) (l:list B) (default : B): B :=
    match n, l with
      | O, x :: l' => x
      | O, nil => default
      | S m, nil => default
      | S m, x :: l' => nth m l' default
    end.

Lemma map_nth {A' B'} (f : A' -> B'): forall l d n,
nth n (map f l) (f d) = f (nth n l d).
Proof.
  induction l; destruct n; cbn; intros; try reflexivity; eauto.
Defined.

Lemma nth_overflow {A'} : forall (l : list A') n d, length l <= n -> nth n l d = d.
Proof.
  induction l; destruct n; cbn; intros; try reflexivity. 
  - inversion H. 
  - eapply IHl. lia_comp.
Defined. 

Lemma nth_indep {A'} : forall (l : list A') n d d', n < length l -> nth n l d = nth n l d'.
Proof.
  induction l; cbn; intros. inversion H. destruct n; try reflexivity. eapply IHl. lia_comp.
Defined. 

Fixpoint seq (start len:nat) : list nat :=
  match len with
    | 0 => nil
    | S len => start :: seq (S start) len
  end.

Lemma seq_nth : forall len start n d,
  n < len -> (nth n (seq start len) d) = (plus start n).
Proof.
  intro len; induction len as [|len IHlen]; intros start n d H.
  - inversion H.
  - simpl seq.
    destruct n; simpl.
    + lia_comp.
    + rewrite IHlen; eauto. lia_comp. 
Defined.

Lemma seq_length : forall len start, length (seq start len) = len.
  intro len; induction len; simpl; intros.
  + reflexivity.
  + f_equal; eauto. 
Defined.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l; cbn.
  - reflexivity.
  - f_equal; eauto. 
Defined.

Lemma seq_shift : forall len start,
map S (seq start len) = seq (S start) len.
Proof.
  intro len; induction len as [|len IHlen]; simpl; try reflexivity.
  intros. rewrite IHlen. reflexivity.
Defined.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
  induction l; cbn; try reflexivity. 
  rewrite H. f_equal; eauto.
Defined.

Reserved Notation "↑ d t" (at level 27, d at level 0, t at level 0).
Reserved Notation "t [ n ↦ u ]" (at level 26, left associativity).
Reserved Notation "⇑ d t" (at level 27, d at level 0, t at level 0).
Reserved Notation "t [[ n ↦ s ]]" (at level 26, left associativity).
Reserved Notation "⇧ d t" (at level 27, d at level 0, t at level 0).
Reserved Notation "# n" (at level 25, n at level 0).
Reserved Notation "'λ' t" (at level 28, t at level 0).
Reserved Notation "t1 @ t2" (at level 29, left associativity).
Reserved Notation "& n" (at level 25).
Reserved Notation "∀ ty" (at level 28).
Reserved Notation "ty1 ⇒ ty2" (at level 30, right associativity).
Reserved Notation "t ≻ t'" (at level 70, no associativity).
Reserved Notation "t ≻* t'" (at level 70, no associativity).
Reserved Notation "t ≻' t'" (at level 70, no associativity).
Reserved Notation "t ≻'* t'" (at level 70, no associativity).
Reserved Notation "t ≻₀ t'" (at level 70, no associativity).
Reserved Notation "t ≻₀* t'" (at level 70, no associativity).
Reserved Notation "X <-> Y" (at level 95, no associativity).
Reserved Notation "X <~> Y" (at level 95, no associativity).
Reserved Notation "X <~~> Y" (at level 95, no associativity).
Reserved Notation " t_ctx ⊩ term ∈ type " (at level 70, no associativity).
Reserved Notation " ctx ⊢ term ¦ type " (at level 70, no associativity).
Reserved Notation "p … n -1" (at level 30, no associativity).
Set Implicit Arguments.
Open Scope type_scope.
(** * Equivalences

  Some definitions and lemmas about equivalences *)
Lemma iff_forall : forall (A : Type) (P Q R : (A -> Prop) -> Prop),
  (forall X, R X -> (P X <-> Q X))
    -> ((forall X, R X -> P X) <-> (forall X, R X -> Q X)).
Proof.
intros A P Q R H.
split; intros H' X HX; apply H; try apply H'; apply HX.
Defined.
Definition iffE (A : Type) (X Y : A -> Prop) : Prop :=
  forall (a : A), (X a) <-> (Y a).
Infix "<~>" := iffE.
Lemma iffE_trans : forall (A : Type) (X Y Z : A -> Prop),
  (X <~> Y) -> (Y <~> Z) -> (X <~> Z).
Proof.
simpl.
intros A X Y Z Heq1 Heq2 t.
split; intro H.
apply Heq2; apply Heq1; assumption.
apply Heq1; apply Heq2; assumption.
Defined.
Lemma iffE_forall : forall (A : Type) (P Q P' Q' : A -> Prop),
  (P <~> Q)
    -> (P' <~> Q')
    -> ((forall X, P X -> P' X) <-> (forall X, Q X -> Q' X)).
Proof.
intros A P Q P' Q' H H'.
split; intros H0 X HX; apply H'; apply H0; apply H; apply HX.
Defined.
Definition iffE2 (A B : Type) (X Y : A -> B -> Prop) :=
  forall (a : A), (X a <~> Y a).
Infix "<~~>" := iffE2.
Lemma iffE2_trans : forall (A B : Type) (X Y Z : A -> B -> Prop),
  (X<~~> Y) -> (Y <~~> Z) -> (X <~~> Z).
Proof.
simpl.
intros A B X Y Z Heq1 Heq2 n t.
split; intro H.
apply Heq2; apply Heq1; assumption.
apply Heq1; apply Heq2; assumption.
Defined.
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
Notation Tree := (@MakeTree A).
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
  d <= n -> ↑d(#n) = #(S n).
Proof.
intros d n Hge0.
unfold shift. apply reflectLeq in Hge0. rewrite Hge0. reflexivity.
Defined.
Lemma shift_leaf2 : forall (d n : nat),
  n < d -> ↑d(#n) = #n.
Proof.
intros d n Hlt.
unfold shift.
rewrite leb_correct_conv; eauto. eapply reflectLt; eauto. 
Defined.
Lemma shift_bind : forall (d : nat) (t : Tree),
  ↑d(λ t) = λ(↑(S d) t).
Proof.
reflexivity.
Defined.
Lemma shift_node : forall (d : nat) (t t' : Tree),
  ↑d(t@t') = (↑d t)@(↑d t').
Proof.
reflexivity.
Defined.
Lemma shift_shift : forall (d d' : nat) (t : Tree),
  d' <= d -> ↑d'(↑d t) = ↑(S d)(↑d' t).
Proof.
intros d d' t.
revert d d'.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intros d d' Hle.
*case (le_dec d n); intro Hdec.
 +rewrite 4 shift_leaf1 by lia_comp.
  reflexivity.
 +case (le_dec d' n); intro Hdec'.
  -rewrite shift_leaf2, shift_leaf1, shift_leaf2 by lia_comp.
   reflexivity.
  -rewrite 3 shift_leaf2 by lia_comp.
   reflexivity.
*rewrite 4 shift_bind.
 f_equal.
 rewrite IH by lia_comp.
 reflexivity.
*rewrite 4 shift_node.
 f_equal.
 +rewrite IH1 by lia_comp.
  reflexivity.
 +rewrite IH2 by lia_comp.
  reflexivity.
Defined.
(** [substitute n t t'] substitutes [t'] for the free variable of
  index [n] in [t], and decreases all the free variables of [t]
  which have an index > [n] *)
Fixpoint substitute (n : nat) (tree tree' : Tree) : Tree :=
  match tree with
    | Leaf m => match m ?= n with Eq => tree' | Lt => #m | Gt => #(Nat.pred m) end
    | Bind t => λ(substitute (S n) t (↑0 tree'))
    | Node t1 t2 => (substitute n t1 tree')@(substitute n t2 tree')
  end.
Notation "t [ n ↦ u ]" := (substitute n t u).
Lemma substitute_leaf1 : forall (n : nat) (t : Tree),
  #n[n↦t] = t.
Proof.
intros n t.
unfold substitute.
rewrite (proj2 (compare_eq_iff _ _)) by reflexivity.
reflexivity.
Defined.
Lemma substitute_leaf2 : forall (n m : nat) (t : Tree),
  m > n -> #m[n↦t] = #(Nat.pred m).
Proof.
intros n m t Hgt.
unfold substitute.
rewrite (proj1 (nat_compare_gt _ _)) by assumption.
reflexivity.
Defined.
Lemma substitute_leaf3 : forall (n m : nat) (t : Tree),
  m < n -> #m[n↦t] = #m.
Proof.
intros n m t Hgt.
unfold substitute.
rewrite (proj1 (nat_compare_lt _ _)) by assumption.
reflexivity.
Defined.
Lemma substitute_bind : forall (n : nat) (t t' : Tree),
  (λ t)[n↦t'] = λ(t[S n↦↑0 t']).
Proof.
reflexivity.
Defined.
Lemma substitute_node : forall (n : nat) (t1 t2 t' : Tree),
  (t1@t2)[n↦t'] = t1[n↦t']@t2[n↦t'].
Proof.
reflexivity.
Defined.
Lemma shift_substitute1 : forall (n d : nat) (t t' : Tree),
  d <= n -> (↑d t)[S n↦↑d t'] = ↑d (t[n↦t']).
Proof.
intros n d t t'.
revert n d t'.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n d t' Hle.
*case (compare_spec n m); intro Hdec.
 +rewrite Hdec.
  rewrite shift_leaf1, 2 substitute_leaf1 by lia_comp.
  reflexivity.
 +rewrite shift_leaf1, 2 substitute_leaf2, shift_leaf1 by lia_comp.
  f_equal; lia_comp.
 +case (le_dec d m); intro Hdec'.
  -rewrite substitute_leaf3, shift_leaf1, substitute_leaf3 by lia_comp.
   reflexivity.
  -rewrite substitute_leaf3, shift_leaf2, substitute_leaf3 by lia_comp.
   reflexivity.
*rewrite shift_bind, 2 substitute_bind, shift_bind.
 f_equal.
 rewrite shift_shift by lia_comp.
 rewrite IH by lia_comp.
 reflexivity.
*rewrite shift_node, 2 substitute_node, shift_node.
 f_equal.
 +rewrite IH1 by lia_comp.
  reflexivity.
 +rewrite IH2 by lia_comp.
  reflexivity.
Defined.
Lemma shift_substitute2 : forall (n d : nat) (t t' : Tree),
  d >= n -> (↑(S d) t)[n↦↑d t'] = ↑d(t[n↦t']).
Proof.
intros n d t t'.
revert n d t'.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n d t' Hle.
*case (compare_spec n m); intro Hdec.
 +rewrite Hdec.
  rewrite shift_leaf2, 2 substitute_leaf1 by lia_comp.
  reflexivity.
 +case (le_dec (S d) m); intro Hdec'.
  -rewrite substitute_leaf2, shift_leaf1, substitute_leaf2, shift_leaf1 by lia_comp.
   f_equal; lia_comp.
  -rewrite substitute_leaf2, shift_leaf2, substitute_leaf2, shift_leaf2 by lia_comp.
   reflexivity.
 +rewrite shift_leaf2, 2 substitute_leaf3, shift_leaf2 by lia_comp.
  reflexivity.
*rewrite shift_bind, 2 substitute_bind, shift_bind.
 f_equal.
 rewrite shift_shift by lia_comp.
 rewrite IH by lia_comp.
 reflexivity.
*rewrite shift_node, 2 substitute_node, shift_node.
 f_equal.
 +rewrite IH1 by lia_comp.
  reflexivity.
 +rewrite IH2 by lia_comp.
  reflexivity.
Defined.
Lemma shift_substitute3 : forall (d : nat) (t t' : Tree),
  (↑d t)[d↦t'] = t.
Proof.
intros d t.
revert d.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intros d t'.
*case (le_dec d n); intro Hdec.
 +rewrite shift_leaf1, substitute_leaf2 by lia_comp.
  reflexivity.
 +rewrite shift_leaf2, substitute_leaf3 by lia_comp.
  reflexivity.
*rewrite shift_bind, substitute_bind.
 f_equal.
 apply IH.
*rewrite shift_node, substitute_node.
 f_equal.
 +apply IH1.
 +apply IH2.
Defined.
Lemma substitute_substitute : forall (n n' : nat) (t t' t'' : Tree),
  n <= n' -> t[n↦t'][n'↦t''] = t[S n'↦↑n t''][n↦t'[n'↦t''] ].
Proof.
intros n n' t t' t'' Hle.
revert n n' Hle t' t''.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n n' Hle t' t''.
*case (compare_spec n m); intro Hdec.
 +rewrite Hdec.
  rewrite substitute_leaf1, substitute_leaf3, substitute_leaf1 by lia_comp.
  reflexivity.
 +case (compare_spec (S n') m); intro Hdec'.
  -rewrite <- Hdec'.
   rewrite substitute_leaf2, 2 substitute_leaf1, shift_substitute3 by lia_comp.
   reflexivity.
  -rewrite 4 substitute_leaf2 by lia_comp.
   reflexivity.
  -rewrite substitute_leaf2, 2 substitute_leaf3, substitute_leaf2 by lia_comp.
   reflexivity.
 +rewrite 4 substitute_leaf3 by lia_comp.
  reflexivity.
*rewrite 4 substitute_bind.
 f_equal.
 rewrite IH by lia_comp.
 rewrite shift_substitute1, <- shift_shift by lia_comp.
 reflexivity.
*rewrite 4 substitute_node.
 f_equal.
 +rewrite IH1 by lia_comp.
  reflexivity.
 +rewrite IH2 by lia_comp.
  reflexivity.
Defined.
(** [free_var t] picks the least index n such that every free variable
  appearing in [t] has index < n *)
Fixpoint free_var (tree : Tree) :=
  match tree with
    | Leaf n => S n
    | Bind t => Nat.pred (free_var t)
    | Node t1 t2 => max (free_var t1) (free_var t2)
  end.
Lemma free_var_leaf : forall (n : nat), free_var (#n) = S n.
Proof.
intro n.
reflexivity.
Defined.
Lemma free_var_bind : forall (t : Tree),
  free_var (λ t) = Nat.pred (free_var t).
Proof.
intro t.
reflexivity.
Defined.
Lemma free_var_node : forall (t1 t2 : Tree),
  free_var (t1@t2) = max (free_var t1) (free_var t2).
Proof.
intros t1 t2.
reflexivity.
Defined.
Lemma shift_free_var : forall (t : Tree) (d : nat),
  d >= free_var t -> ↑d t = t.
Proof.
intro t.
induction t as [ n | t IH | t1 IH1 t2 IH2 ]; intro d.
*rewrite free_var_leaf; intro Hge.
 rewrite shift_leaf2 by lia_comp.
 reflexivity.
*rewrite free_var_bind; intro Hge.
 rewrite shift_bind.
 f_equal.
 apply IH.
 lia_comp.
*rewrite free_var_node; intro Hge.
 rewrite shift_node.
 f_equal.
 +apply IH1. lia_comp. 
 +apply IH2. lia_comp.
Defined.
Lemma substitute_free_var : forall (t : Tree) (n : nat) (t' : Tree),
  n >= free_var t -> t[n↦t'] = t.
intro t.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n t'.
*rewrite free_var_leaf; intro Hge.
 rewrite substitute_leaf3 by lia_comp.
 reflexivity.
*rewrite free_var_bind; intro Hge.
 rewrite substitute_bind.
 f_equal.
 apply IH.
 lia_comp.
*rewrite free_var_node; intro Hge.
 rewrite substitute_node.
 f_equal.
 +apply IH1. lia_comp.
 +apply IH2. lia_comp.
Defined.
(** This lemma states that the substitution of a big enough variable
  for any given variable can be reverted *)
Lemma id_substitute_shift_substitute : forall (t : Tree) (n p : nat),
  n >= free_var t -> (↑p (t[p↦#n]))[S n↦#p] = t.
Proof.
intro t; induction t as [ q | t IH | t1 IH1 t2 IH2 ]; intros n p.
rewrite free_var_leaf; intro Hge.
* case (compare_spec p q); intro Hdec.
 +rewrite Hdec.
  rewrite substitute_leaf1, shift_leaf1, substitute_leaf1 by lia_comp.
  reflexivity.
 +rewrite substitute_leaf2, shift_leaf1, substitute_leaf3 by lia_comp.
  f_equal.
  lia_comp.
 +rewrite substitute_leaf3, shift_leaf2, substitute_leaf3 by lia_comp.
  reflexivity.
*rewrite free_var_bind; intro Hge.
 rewrite substitute_bind, shift_bind, substitute_bind.
 f_equal.
 rewrite 2 shift_leaf1 by lia_comp.
 apply IH; lia_comp.
*rewrite free_var_node; intro Hge.
 rewrite substitute_node, shift_node, substitute_node.
 f_equal.
 +apply IH1.
  lia_comp.
 +apply IH2.
  lia_comp.
Defined.
(** [shift_list d s] performs [shift d t] for every [t] of [s].
  This will be used in the definition of parallel substitution *)
Definition shift_list (depth : nat) (trees : list Tree) : list Tree :=
  map (fun tree : Tree => ↑depth tree) trees.
Notation "⇑ d t" := (shift_list d t).
Lemma shift_list_nil : forall (d : nat), ⇑d nil = nil.
Proof.
intro d.
unfold shift_list.
reflexivity.
Defined.
Lemma shift_list_cons : forall (d : nat) (t : Tree) (trees : list Tree),
  ⇑d (t::trees) = ↑d t :: ⇑d trees.
Proof.
intro d.
unfold shift_list.
reflexivity.
Defined.
Lemma shift_list_length : forall (d : nat) (trees : list Tree),
  length (⇑d trees) = length trees.
Proof.
intros d trees.
unfold shift_list.
apply map_length.
Defined.
Lemma shift_list_nth : forall (d : nat) (trees : list Tree) (n : nat) (t : Tree),
  nth n (⇑d trees) (↑d t) = ↑d (nth n trees t).
Proof.
intros d trees n t.
unfold shift_list.
apply map_nth.
Defined.
Lemma shift_list_shift_list : forall (d d' : nat) (trees : list Tree),
  d' <= d -> ⇑d'(⇑d trees) = ⇑(S d)(⇑d' trees).
Proof.
intros d d' trees Hle.
induction trees as [ | t trees IH ].
*rewrite 2 shift_list_nil.
 reflexivity.
*rewrite 4 shift_list_cons, shift_shift by lia_comp.
 rewrite IH.
 reflexivity.
Defined.
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
  m >= n -> #m[[n↦s]] = nth (m - n) s (#(m - length s)).
Proof.
intros n m s Hge.
unfold substitute_list.
rewrite reflectLeq by lia_comp.
reflexivity.
Defined.
Lemma substitute_list_leaf2 : forall (n m : nat) (s : list Tree),
  m < n -> #m[[n↦s]] = #m.
Proof.
intros n m s Hge.
unfold substitute_list.
rewrite leb_correct_conv by (eapply reflectLt; eauto).
reflexivity.
Defined.
Lemma substitute_list_bind : forall (n : nat) (t : Tree) (s : list Tree),
  (λ t)[[n↦s]] = λ (t[[S n↦⇑0 s]]).
Proof.
intros n t s.
reflexivity.
Defined.
Lemma substitute_list_node : forall (n : nat) (t1 t2 : Tree) (s : list Tree),
  (t1@t2)[[n↦s]] = t1[[n↦s]]@t2[[n↦s]].
Proof.
intros n t1 t2 s.
reflexivity.
Defined.
Lemma substitute_list_nil : forall (n : nat) (t : Tree), t[[n↦nil]] = t.
Proof.
intros n t; revert n.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intro n.
*case (le_dec n m); intro Hdec.
 +rewrite substitute_list_leaf1 by lia_comp.
  rewrite nth_overflow; [ | simpl; lia_comp ].
  f_equal; simpl; lia_comp.
 +rewrite substitute_list_leaf2 by lia_comp.
  reflexivity.
*rewrite substitute_list_bind.
 f_equal.
 rewrite IH; reflexivity.
*rewrite substitute_list_node.
 f_equal.
 +rewrite IH1; reflexivity.
 +rewrite IH2; reflexivity.
Defined.
Lemma substitute_list_cons : forall (n : nat) (t : Tree) (s : list Tree) (t' : Tree),
  t[[n↦t'::s]] = t[[S n↦⇑n s]][n↦t'].
Proof.
intros n t; revert n.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n s t'.
*case (compare_spec n m); intro Hdec.
 +rewrite Hdec.
  rewrite substitute_list_leaf1, substitute_list_leaf2, substitute_leaf1 by lia_comp.
  replace (m - m) with 0 by lia_comp; simpl nth.
  reflexivity.
 +rewrite 2 substitute_list_leaf1, shift_list_length by lia_comp.
  destruct m as [ | m ]; [ inversion Hdec | ].
  replace (S m - n) with (S (m - n)) by lia_comp; simpl nth at 1.
  replace (S m - S n) with (m - n) by lia_comp.
  rewrite <- (shift_substitute3 n _ t'); f_equal.
  rewrite <- shift_list_nth.
  case (lt_dec (m - n) (length s)); intro Hdec'.
  -apply nth_indep.
   rewrite shift_list_length; lia_comp.
  -f_equal.
   rewrite shift_leaf1 by lia_comp.
   f_equal; lia_comp.
 +rewrite 2 substitute_list_leaf2, substitute_leaf3 by lia_comp.
  reflexivity.
*rewrite 2 substitute_list_bind, substitute_bind, shift_list_cons, shift_list_shift_list by lia_comp.
 f_equal; apply IH.
*rewrite 2 substitute_list_node, substitute_node.
 f_equal.
 +apply IH1.
 +apply IH2.
Defined.
(** [var_seq p n] is the list of variables of index  [p] to [n-1] *)
Definition var_seq (p n : nat) : list Tree :=
  map (fun n => #n) (seq p (n - p)).
Notation "p … n -1" := (var_seq p n).
Lemma var_nil : forall (p n : nat), p >= n -> (p…n-1) = nil.
Proof.
intros n p Hle.
unfold var_seq.
replace (p - n) with 0 by lia_comp.
reflexivity.
Defined.
Lemma var_cons : forall (p n : nat),
  p < n -> (p…n-1) = #p::((S p)…n-1).
Proof.
intros n p Hle.
unfold var_seq.
destruct p as [ | p ]; [ inversion Hle | ].
replace (S p - n) with (S (p - n)) by lia_comp.
reflexivity.
Defined.
Lemma var_nth : forall (p n m : nat) (t : Tree),
  m < n - p -> nth m (p…n-1) t = #(p + m).
Proof.
intros p n m t Hineq.
unfold var_seq. cbn. 
rewrite (nth_indep _ _ _ (#0)).
*rewrite map_nth, seq_nth by lia_comp.
 f_equal; lia_comp.
*rewrite map_length, seq_length.
 assumption.
Defined.
Lemma var_shift : forall (p n d : nat),
  d <= p -> ⇑d(p…n-1) = (S p)…(S n)-1.
Proof.
intros p n d Hle.
unfold var_seq.
unfold shift_list.
rewrite map_map, <- seq_shift, map_map.
replace (S n - S p) with (n - p) by lia_comp.
generalize (n - p); clear n; intro n.
revert p d Hle.
induction n as [ | n IH ]; intros p d Hle.
*reflexivity.
*simpl seq.
 simpl map.
 rewrite reflectLeq by lia_comp.
 f_equal.
 rewrite <- (IH _ d) by lia_comp.
 apply map_ext.
 reflexivity.
Defined.
Lemma id_subst : forall (t : Tree) (n p : nat),
  n >= free_var t -> t[[p↦p…n-1]] = t.
Proof.
intro t.
induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros n p.
*rewrite free_var_leaf.
 case (le_dec p m); intros Hdec Hle.
 +rewrite substitute_list_leaf1 by lia_comp.
  rewrite var_nth by lia_comp.
  f_equal; lia_comp.
 +rewrite substitute_list_leaf2 by lia_comp.
  reflexivity.
*rewrite free_var_bind; intro Hge.
 rewrite substitute_list_bind, var_shift by lia_comp.
 rewrite IH by lia_comp.
 reflexivity.
*rewrite free_var_node; intro Hge.
 rewrite substitute_list_node.
 rewrite IH1 by lia_comp.
 rewrite IH2 by lia_comp.
 reflexivity.
Defined.
End Substitutions.
(** * Confluence of pure λ-calculus

  In the following, we prove confluence of pure λ-calculus, but
  this is completely independent from the strong normalization proof.
  We follow the proof of Krivine's book "Lambda-Calculus Types and
  Models". *)
Section ReflTransClosure.
Variable A : Type.
(** Here are the definitions of confluence and reflexive
  transitive closure for arbitrary relations *)
Definition confluent (R : A -> A -> Prop) : Prop :=
  forall (t t' t'' : A),
    R t t' ->  R t t'' -> exists t''' : A, R t' t''' /\ R t'' t'''.
Inductive refl_trans_closure (R : A -> A -> Prop) : A -> A -> Prop :=
  | Refl : forall (t : A), refl_trans_closure R t t
  | Trans : forall (t t' t'' : A), (R t t') -> refl_trans_closure R t' t'' -> refl_trans_closure R t t''.
Section Confluent.
Variable R : A -> A -> Prop.
Infix "≻" := R.
Infix "≻*" := (refl_trans_closure R).
Lemma refl_trans_refl : forall (t : A), t ≻* t.
Proof.
intro t.
apply Refl.
Defined.
Lemma refl_trans_trans : forall (t t' t'' : A),
  t ≻* t' -> t' ≻* t'' -> t ≻* t''.
Proof.
intros t t' t'' Hred Hred'.
induction Hred as [ t | t0 t t' Hred0 Hred IH ].
*assumption.
*eapply Trans.
 +apply Hred0.
 +apply IH.
  assumption.
Defined.
Lemma refl_trans_confluent : confluent R -> confluent (refl_trans_closure R).
Proof.
intro Hconfl.
assert (forall (t : A) (t' : A) (t'' : A),
  t ≻* t' -> t ≻ t'' -> exists t''' : A, t' ≻ t''' /\ t'' ≻* t''') as H.
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
Defined.
End Confluent.
Variable R : A -> A -> Prop.
Infix "≻" := R.
Infix "≻*" := (refl_trans_closure R).
Variable R' : A -> A -> Prop.
Infix "≻'" := R'.
Infix "≻'*" := (refl_trans_closure R').
Lemma refl_trans_incl :
  (forall (t : A) (t' : A), t ≻ t' -> t ≻'* t')
   -> (forall (t : A) (t' : A), t ≻* t' -> t ≻'* t').
Proof.
intros Hinc t t' Hred.
induction Hred as [ t | t t' t'' Hred Hred' IH ].
*apply Refl.
*eapply refl_trans_trans.
 +apply Hinc.
  exact Hred.
 +assumption.
Defined.
End ReflTransClosure.
Notation "↑ d t" := (shift d t).
Notation " t [ n ↦ u ]" := (substitute n t u).
Notation "⇑ d t" := (shift_list d t).
Notation " t [[ n ↦ s ]]" := (substitute_list n t s).
Notation "p … n -1" := (var_seq _ p n).
(** TermParam is a custom type allowing notations which are specific
  to λ-terms *)
Inductive TermParam :=.
Abbreviation Term := (@MakeTree TermParam).
Notation "# n" := (@Leaf TermParam n).
Notation "'λ' t" := (@Bind TermParam t).
Infix "@" := (@Node TermParam).
(** Our [red0] is Krivine's ρ *)
Inductive red0 : Term -> Term -> Prop :=
  | Ctx_Var0 : forall (n : nat), red0 (#n) (#n)
  | Beta0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (λ t1@t2) (t1'[0↦t2'])
  | Ctx_Abs0 : forall (t t' : Term), red0 t t' -> red0 (λ t) (λ t')
  | Ctx_App0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (t1@t2) (t1'@t2').
Infix "≻₀" := red0.
Infix "≻₀*" := (refl_trans_closure red0).
Lemma red0_refl : forall (t : Term), t ≻₀ t.
Proof.
intro t.
induction t as [ n | t IH | t1 IH1 t2 IH2 ].
*apply Ctx_Var0.
*apply Ctx_Abs0; assumption.
*apply Ctx_App0; assumption.
Defined.
Lemma red0_shift : forall (t t' : Term) (d : nat),
  t ≻₀ t' -> ↑d t ≻₀ ↑d t'.
Proof.
intros t t' d Hred.
revert d.
induction Hred as [ n | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 | t t' Hred IH | t1 t1' t2 t2' Hred1 IH1 Hred2 IH2 ]; intro d.
*apply red0_refl.
*rewrite shift_node, shift_bind, <- shift_substitute2 by lia_comp.
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
Defined.
Lemma red0_subst : forall (t1 t1' t2 t2' : Term) (n : nat),
  t1 ≻₀ t1' -> t2 ≻₀ t2' ->  t1[n↦t2] ≻₀ t1'[n↦t2'].
Proof.
intros t1 t1' t2 t2' n Hred1 Hred2.
revert t2 t2' Hred2 n.
induction Hred1 as [ m | t11 t11' t12 t12' Hred11 IH1 Hred12 IH2 | t1 t1' Hred1' IH | t11 t11' t12 t12' Hred11 IH1 Hred12 IH2 ]; intros t2 t2' Hred2 n.
*case (CompSpec2Type (compare_spec n m)); intro Hdec.
 +rewrite Hdec.
  rewrite 2 substitute_leaf1.
  assumption.
 +rewrite 2 substitute_leaf2 by lia_comp.
  apply Ctx_Var0.
 +rewrite 2 substitute_leaf3 by lia_comp.
  apply Ctx_Var0.
*rewrite substitute_node, substitute_bind, substitute_substitute by lia_comp.
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
Defined.
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
Defined.
 (** Our [beta] is Krivine's β₀ *)
Inductive beta : Term -> Term -> Prop :=
  | Beta : forall (t t' : Term), beta ((λ t)@t') (t[0↦t'])
  | Ctx_Abs : forall (t t' : Term), beta t t' -> beta (λ t) (λ t')
  | Ctx_App_l : forall (t1 t1' : Term) (t2 : Term), beta t1 t1' -> beta (t1@t2) (t1'@t2)
  | Ctx_App_r : forall (t1 t2 : Term) (t2' : Term), beta t2 t2' -> beta (t1@t2) (t1@t2').
Infix "≻" := beta.
Infix "≻*" := (refl_trans_closure beta).
Lemma beta_red0_incl : forall (t t' : Term), t ≻ t' -> t ≻₀ t'.
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
Defined.
Lemma beta_substitute : forall (t t' t'' : Term) (n : nat),
  t ≻ t' -> t[n↦t''] ≻ t'[n↦t''].
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
 +rewrite substitute_node, substitute_bind, substitute_substitute by lia_comp.
  apply Beta.
 +rewrite 2 substitute_node.
  apply Ctx_App_l.
  apply IH1.
  assumption.
 +rewrite 2 substitute_node.
  apply Ctx_App_r.
  apply IH2.
  assumption.
Defined.
Lemma shift_beta : forall (t t' : Term) (d : nat),
  ↑d t ≻ t' -> exists t'' : Term, t ≻ t'' /\ t' = ↑d t''.
Proof.
intro t; induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros t' d.
*case (le_dec d m); intro Hdec.
 +rewrite shift_leaf1 by lia_comp.
  intro Hred; inversion Hred.
 +rewrite shift_leaf2 by lia_comp.
  intro Hred; inversion Hred.
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
  -case (le_dec d m); intro Hdec; [ rewrite shift_leaf1 by lia_comp | rewrite shift_leaf2 by lia_comp ]; discriminate.
  -rewrite shift_bind.
   intro Heqt1; injection Heqt1; clear Heqt1.
   intro Heqt1; rewrite Heqt1; clear t01 Heqt1.
   exists (t1[0↦t2]).
   split; [ apply Beta | ].
   apply shift_substitute2; lia_comp.
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
Defined.
Lemma substitute_leaf_beta : forall (t t' : Term) (p q : nat),
  t[p↦#q] ≻ t' -> exists t'' : Term,  t ≻ t'' /\ t' = t''[p↦#q].
Proof.
intro t; induction t as [ m | t IH | t1 IH1 t2 IH2 ]; intros t' p q.
*case (CompSpec2Type (compare_spec p m)); intro Hdec.
 +rewrite Hdec.
  rewrite substitute_leaf1.
  intro Hred; inversion Hred.
 +rewrite substitute_leaf2 by lia_comp.
  intro Hred; inversion Hred.
 +rewrite substitute_leaf3 by lia_comp.
  intro Hred; inversion Hred.
*rewrite substitute_bind.
 intro Hred; inversion_clear Hred as [ | t'' t''' Hred' | | ].
 clear t'.
 edestruct IH as [ t' [ Hredt' Heqt' ] ]; [ exact Hred' | ].
 exists (λ t').
 split; [ apply Ctx_Abs; exact Hredt' | ].
 rewrite substitute_bind.
 rewrite Heqt'.
 rewrite shift_leaf1 by lia_comp.
 reflexivity.
*rewrite substitute_node.
 remember (t1[p↦#q]) as t001 eqn:Heqt1; intro Hred; revert Heqt1.
 inversion_clear Hred as [ t01 t02 | | t01 t01' t02 Hred01 | t01 t02 t02' Hred02 ].
 +clear t001 IH1 IH2.
  destruct t1 as [ m | t1 | t11 t12 ].
  -case (CompSpec2Type (compare_spec p m)); intro Hdec; [ rewrite Hdec; rewrite substitute_leaf1 by lia_comp | rewrite substitute_leaf2 by lia_comp | rewrite substitute_leaf3 by lia_comp ]; discriminate.
  -rewrite substitute_bind.
   intro Heqt1; injection Heqt1; clear Heqt1.
   intro Heqt1; rewrite Heqt1; clear t01 Heqt1.
   exists (t1[0↦t2]).
   split; [ apply Beta | ].
   symmetry; apply substitute_substitute; lia_comp.
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
Defined.
Lemma beta_cl_leaf : forall (n : nat), #n ≻* #n.
Proof.
intro n.
apply Refl.
Defined.
Lemma beta_cl_bind : forall (t t' : Term), t ≻* t' -> λ t ≻* λ t'.
Proof.
intros t t' Hred.
induction Hred as [ t | t t' t'' Hred Hred' IH ].
*apply Refl.
*eapply Trans.
 +apply Ctx_Abs.
  exact Hred.
 +assumption.
Defined.
Lemma beta_cl_node : forall (t1 t1' t2 t2' : Term),
  t1 ≻* t1' -> t2 ≻* t2' -> t1@t2 ≻* t1'@t2'.
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
Defined.
Lemma red0_beta_cl_incl : forall (t t' : Term), t ≻₀ t' -> t ≻* t'.
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
Defined.
Lemma red0_beta_equiv : forall (t t' : Term), t ≻₀* t' <-> t ≻* t'.
Proof.
intros t t'.
split.
*apply refl_trans_incl.
 apply red0_beta_cl_incl.
*apply refl_trans_incl.
 clear t t'; intros t t' Hred.
 eapply Trans; [ | apply Refl ].
 apply beta_red0_incl; assumption.
Defined.
Lemma beta_cl_confluent : confluent (refl_trans_closure beta).
Proof.
assert (confluent (refl_trans_closure red0)) as red0_conf.
*apply refl_trans_confluent.
 apply red0_confluent.
*intros t t1 t2.
 intro Hred1; generalize (proj2 (red0_beta_equiv _ _) Hred1); clear Hred1; intro Hred1.
 intro Hred2; generalize (proj2 (red0_beta_equiv _ _) Hred2); clear Hred2; intro Hred2.
 edestruct red0_conf as  [ t' Hred ]; [ exact Hred1 | exact Hred2 | ]; clear red0_conf Hred1 Hred2.
 destruct Hred as [ Hred1 Hred2 ].
 exists t'.
 split; apply red0_beta_equiv; assumption.
Defined.
(** * Strong normalization of system F

  We now move to the strong normalization proof. We follow the
  proof of Girard-Taylor-Lafont's "Proofs and Types"
  ----
  The set of normalizing terms is inductively defined *)
Inductive Normalizing (t : Term) : Prop :=
  | NormalizingInd : (forall (t' : Term), t ≻ t' -> Normalizing t') -> Normalizing t.
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
Defined.
Lemma normalizing_app : forall (t1 t2 : Term),
  Normalizing (t1@t2) -> Normalizing t1 /\ Normalizing t2.
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
Defined.
Lemma var_normalizing : forall (n : nat), Normalizing (#n).
Proof.
intro n; apply NormalizingInd; intros t Hred; inversion Hred.
Defined.
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
Defined.
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
Defined.
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
Defined.
(** This innocent-looking lemma is essential in the λ-introduction case
  of the normalization proof *)
Lemma normalizing_substitute_leaf : forall (t : Term),
  (forall (n : nat), Normalizing (t[0↦#n])) -> Normalizing t.
Proof.
intros t Ht.
rewrite <- (@id_substitute_shift_substitute _ _ (free_var t) 0) by lia_comp.
apply substitute_leaf_normalizing.
apply shift_normalizing.
apply Ht.
Defined.
(** Definition of closure under β-reduction *)
Definition RedClosed (X : Term -> Prop) : Prop :=
  forall (t t' : Term), X t -> t ≻ t' -> X t'.
(** A term is neutral if it is not an abstraction *)
Inductive Neutral : Term -> Prop :=
  | Var_Neutral : forall (n : nat), Neutral (#n)
  | App_Neutral : forall (t1 t2 : Term), Neutral (t1@t2).
(** A set of terms is saturated if a neutral term is in the set
  whenever any one-step reduction of the term is in the set *)
Definition Saturated (X : Term -> Prop) :=
  forall (t : Term), Neutral t -> (forall (t' : Term), t ≻ t' -> X t') -> X t.
(** A reducibility candidate is a reduction-closed saturated set
  of normalizing terms *)
Definition RedCand (X : Term -> Prop) :=
  (forall (t : Term), X t -> Normalizing t) /\ RedClosed X /\ Saturated X.
Lemma RedCand_Normalizing : forall (X : Term -> Prop),
  RedCand X -> forall (t : Term), X t -> Normalizing t.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Defined.
Lemma RedCand_RedClosed : forall (X : Term -> Prop), RedCand X -> RedClosed X.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Defined.
Lemma RedCand_Saturated : forall (X : Term -> Prop),
  RedCand X -> Saturated X.
Proof.
intros X Hrc.
destruct Hrc as [ Hrc [ Hnorm Hprogress ] ]; tauto.
Defined.
(** A reducibility candidate contains all the variables *)
Lemma RedCandVar : forall (X : Term -> Prop) (n : nat), RedCand X -> X (#n).
Proof.
intros X n Hrc.
apply RedCand_Saturated.
*assumption.
*apply Var_Neutral.
*intros t' Hred.
 inversion Hred.
Defined.
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
Defined.
(** We build the arrow of any two sets of terms *)
Definition RedCandArrow (X Y : Term -> Prop) (t1 : Term) : Prop :=
  forall (t2 : Term), X t2 -> Y (t1@t2).
(** The arrow of two reducibility candidates is a reducibility candidate *)
Lemma red_cand_arrow_RedCand : forall (X Y : Term -> Prop),
  RedCand X -> RedCand Y -> RedCand (RedCandArrow X Y).
Proof.
intros X Y Hrc1 Hrc2.
split; [ | split ].
*intros t1 Ht1.
 eapply proj1; apply (@normalizing_app t1 (#0)).
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
Defined.
(** If [X] and [Y] are two reducibility candidates and if [t1] is a term
  such that for any [t1]∈X, [t1[0↦t2]]∈Y, then λt1∈X *)
Lemma red_cand_arrow_substitute : forall (X Y : Term -> Prop) (t1 : Term),
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
Defined.
(** A type context is the assignment of a set of terms for each
  type variable. If [t_ctx] is such a type context and ix [X] is
  a set of terms, then [shift_t_ctx d t_ctx X] is the type context
  obtained by assigning to n + 1 the set that was assigned to n in
  t_ctx, and assigning [X] to 0 *)
Definition shift_t_ctx (d : nat) (t_ctx : nat -> Term -> Prop) (X : Term -> Prop) : nat -> Term -> Prop :=
  fun n => match Nat.compare n d with Eq => X | Lt => t_ctx n | Gt => t_ctx (Nat.pred n) end.
Notation "⇧ d t" := (shift_t_ctx d t).
Lemma shift_t_ctx1 : forall (d : nat) (t_ctx : nat -> Term -> Prop) (X : Term -> Prop),
  ⇧d t_ctx X d = X.
Proof.
intros d t_ctx X.
unfold shift_t_ctx.
rewrite (proj2 (compare_eq_iff _ _)) by reflexivity.
reflexivity.
Defined.
Lemma shift_t_ctx2 : forall (d : nat) (t_ctx : nat -> Term -> Prop) (X : Term -> Prop) (n : nat),
  n >= d -> ⇧d t_ctx X (S n) = t_ctx n.
Proof.
intros d t_ctx X n Hge.
unfold shift_t_ctx.
rewrite (proj1 (nat_compare_gt _ _)) by lia_comp.
reflexivity.
Defined.
Lemma shift_t_ctx3 : forall (d : nat) (t_ctx : nat -> Term -> Prop) (X : Term -> Prop) (n : nat),
  n < d -> ⇧d t_ctx X n = t_ctx n.
Proof.
intros d t_ctx X n Hlt.
unfold shift_t_ctx.
rewrite (proj1 (nat_compare_lt _ _)) by lia_comp.
reflexivity.
Defined.
Lemma shift_t_ctx_ext1 : forall (t_ctx : nat -> Term -> Prop) (X Y : Term -> Prop),
  (X <~> Y) -> forall (d : nat), ⇧d t_ctx X <~~> ⇧d t_ctx Y.
Proof.
simpl.
intros t_ctx X Y Heq d n term.
case (CompSpec2Type (compare_spec n d)); intro Hdec.
*rewrite Hdec.
 rewrite 2 shift_t_ctx1.
 apply Heq.
*rewrite 2 shift_t_ctx3 by lia_comp.
 unfold iffE; tauto.
*destruct n; [ inversion Hdec | ].
 rewrite 2 shift_t_ctx2 by lia_comp.
 unfold iffE; tauto.
Defined.
Lemma shift_t_ctx_ext2 : forall (t_ctx t_ctx' : nat -> Term -> Prop) (X : Term -> Prop),
  (t_ctx <~~> t_ctx') -> forall (d : nat), ⇧d t_ctx X <~~> ⇧d t_ctx' X.
Proof.
simpl.
intros t_ctx t_ctx' X Heq d n t.
case (CompSpec2Type (compare_spec n d)); intro Hdec.
*rewrite Hdec.
 rewrite 2 shift_t_ctx1.
 unfold iffE; tauto.
*rewrite 2 shift_t_ctx3 by lia_comp.
 apply Heq.
*destruct n as [ | n ]; [ inversion Hdec | ].
 rewrite 2 shift_t_ctx2 by lia_comp.
 apply Heq.
Defined.
Lemma shift_shift_t_ctx : forall (t_ctx : nat -> Term -> Prop) (X Y : Term -> Prop) (d : nat),
  ⇧0 (⇧d t_ctx X) Y <~~> ⇧(S d) (⇧0 t_ctx Y) X.
Proof.
simpl.
intros t_ctx X Y d n term.
case (CompSpec2Type (compare_spec n (S d))); intro Hdec.
*rewrite Hdec.
 rewrite shift_t_ctx1, shift_t_ctx2, shift_t_ctx1 by lia_comp.
 unfold iffE; tauto.
*rewrite (@shift_t_ctx3 (S d)) by lia_comp.
 destruct n as [ | n ].
 +rewrite 2 shift_t_ctx1.
  unfold iffE; tauto.
 +rewrite 2 shift_t_ctx2, shift_t_ctx3 by lia_comp.
  unfold iffE; tauto.
*destruct n as [ | n ]; [ inversion Hdec | ].
 rewrite 2 shift_t_ctx2 by lia_comp.
 destruct n as [ | n ]. inversion Hdec; inversion H0.
 rewrite 2 shift_t_ctx2 by lia_comp.
 unfold iffE; tauto.
Defined.
(** TypeParam is a custom type allowing notations which are specific
  to System F types *)
Inductive TypeFParam :=.
Abbreviation TypeF := (@MakeTree TypeFParam).
Notation "& n" := (@Leaf TypeFParam n).
Notation "∀ ty" := (@Bind TypeFParam ty).
Infix "⇒" := (@Node TypeFParam).
(** In a given type context, we associate to every type
  a set of terms *)
Fixpoint red_cand (t_ctx : nat -> Term -> Prop) (ty : TypeF) (t : Term) : Prop :=
  match ty with
    | Leaf n => t_ctx n t
    | Bind ty => forall (X : Term -> Prop), RedCand X -> red_cand (⇧0 t_ctx X) ty t
    | Node ty ty' => RedCandArrow (red_cand t_ctx ty) (red_cand t_ctx ty') t
  end.
Notation " t_ctx ⊩ t ∈ ty " := (red_cand t_ctx ty t).
Lemma red_cand_atom : forall (t_ctx : nat -> Term -> Prop) (n : nat), red_cand t_ctx (&n) = t_ctx n.
Proof.
reflexivity.
Defined.
Lemma red_cand_forall : forall (t_ctx : nat -> Term -> Prop) (ty : TypeF),
  red_cand t_ctx (∀ty) = fun (t : Term) => forall (X : Term -> Prop), RedCand X -> (⇧0 t_ctx X)⊩t∈ty.
Proof.
reflexivity.
Defined.
Lemma red_cand_arrow : forall (t_ctx : nat -> Term -> Prop) (ty : TypeF) (ty' : TypeF),
  red_cand t_ctx (ty⇒ty') = RedCandArrow (red_cand t_ctx ty) (red_cand t_ctx ty').
Proof.
reflexivity.
Defined.
Lemma red_cand_ext : forall (t_ctx t_ctx' : nat -> Term -> Prop),
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
   unfold iffE; tauto.
  -rewrite 2 shift_t_ctx2 by lia_comp.
   split; apply Heq.
 +intros Ht_ctx' X HrcX.
  eapply IH; [ clear IH Ht_ctx' HrcX | apply Ht_ctx'; exact HrcX ].
  intros n t'.
  destruct n as [ | n ].
  -rewrite 2 shift_t_ctx1.
   unfold iffE; tauto.
  -rewrite 2 shift_t_ctx2 by lia_comp.
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
Defined.
(** If every set of terms in the type context is a reducibility
  candidate, then the set of terms associated to any type is a
  reducibility candidate *)
Lemma red_cand_RedCand : forall (t_ctx : nat -> Term -> Prop) (ty : TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> RedCand (red_cand t_ctx ty).
Proof.
intros t_ctx ty.
revert t_ctx.
induction ty as [ n | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx Ht_ctx.
*rewrite red_cand_atom.
 apply Ht_ctx.
*assert (forall (X : Term -> Prop), RedCand X -> RedCand (red_cand (⇧0 t_ctx X) ty)) as Hrc; [ | clear IH; rename Hrc into IH ].
 +intros X Hrc; apply IH.
  intro n; destruct n; [ rewrite shift_t_ctx1; assumption | rewrite shift_t_ctx2 by lia_comp; apply Ht_ctx ].
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
Defined.
Lemma red_cand_shift : forall (t_ctx : nat -> Term -> Prop) (X : Term -> Prop) (ty : TypeF) (d : nat),
  red_cand t_ctx ty <~> red_cand (⇧d t_ctx X) (↑d ty).
Proof.
intros t_ctx X ty.
revert t_ctx X.
induction ty as [ n | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx X d t.
*case (CompSpec2Type (compare_spec n d)); intro Hdec.
 +rewrite Hdec.
  rewrite shift_leaf1, 2 red_cand_atom, shift_t_ctx2 by lia_comp.
  unfold iffE; tauto.
 +rewrite shift_leaf2, 2 red_cand_atom, shift_t_ctx3 by lia_comp.
  unfold iffE; tauto.
 +rewrite shift_leaf1, 2 red_cand_atom, shift_t_ctx2 by lia_comp.
  unfold iffE; tauto.
*rewrite shift_bind, 2 red_cand_forall.
 split.
 +intros Ht Y HrcY.
  apply (proj2 (@red_cand_ext _ _ (shift_shift_t_ctx _ _ _ _) _ _)).
  apply (proj1 (IH _ _ _ _)).
  apply Ht; assumption.
 +intros Ht Y HrcY.
  apply (proj2 (IH _ X (S d) _)).
  apply (proj1 (@red_cand_ext _ _ (shift_shift_t_ctx _ _ _ _) _ _)).
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
Defined.
Lemma red_cand_shift_substitute : forall (t_ctx : nat -> Term -> Prop) (ty ty' : TypeF) (n : nat),
  red_cand (⇧n t_ctx (red_cand t_ctx ty')) ty <~> red_cand t_ctx (ty[n↦ty']).
Proof.
intros t_ctx ty; revert t_ctx.
induction ty as [ m | ty IH | ty1 IH1 ty2 IH2 ]; intros t_ctx ty' n t.
*rewrite red_cand_atom.
 case (CompSpec2Type (compare_spec m n)); intro Hdec.
 +rewrite Hdec.
  rewrite shift_t_ctx1, substitute_leaf1.
  unfold iff; tauto.
 +rewrite shift_t_ctx3, substitute_leaf3, red_cand_atom by lia_comp.
  unfold iff; tauto.
 +destruct m as [ | m ]; [ inversion Hdec | ].
  rewrite shift_t_ctx2, substitute_leaf2, red_cand_atom by lia_comp.
  unfold iff; tauto.
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
Defined.
(** We define inductively the typing derivations of System F. Since we
  work with de Bruijn indices, a context is just a list of types, where
  the nth element is the type of the variable of index n *)
Inductive TermF : list TypeF -> Term -> TypeF -> Prop :=
  | VarF0 : forall (ctx : list TypeF) (ty : TypeF), TermF (ty :: ctx) (#0) ty
  | VarFS : forall (ctx : list TypeF) (ty : TypeF) (n : nat) (ty' : TypeF), TermF ctx (#n) ty' -> TermF (ty :: ctx) (#(S n)) ty'
  | AbsF : forall (ctx : list TypeF) (ty : TypeF) (t : Term) (ty' : TypeF), TermF (ty :: ctx) t ty' -> TermF ctx (λ t) (ty⇒ty')
  | AppF : forall (ctx : list TypeF) (t : Term) (ty : TypeF) (ty' : TypeF) (t' : Term), TermF ctx t (ty⇒ty') -> TermF ctx t' ty -> TermF ctx (t@t') ty'
  | TAbsF : forall (ctx : list TypeF) (t : Term) (ty : TypeF), TermF (map (fun t => ↑0 t) ctx) t ty -> TermF ctx t (∀ty)
  | TAppF : forall (ctx : list TypeF) (t : Term) (ty : TypeF) (ty' : TypeF), TermF ctx t (∀ty) -> TermF ctx t (ty[0↦ty']).
Notation " ctx ⊢ t ¦ ty " := (TermF ctx t ty).

Lemma context_length : forall (ctx : list TypeF) (ty : TypeF) (n : nat),
  ctx⊢#n¦ty -> length ctx > n.
Proof.
intros ctx ty n Hderiv.
remember (#n) as t eqn:Heq.
revert n Heq.
induction Hderiv as [ ctx ty | ctx ty m ty' Hderiv IH | ctx ty t ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx  t ty Hderiv IH | ctx t ty ty' Hderiv IH ]; intros n Heq.
*injection Heq as Heq'.
 simpl; lia_comp.
*injection Heq as Heq'.
 generalize (IH _ eq_refl). intros ?.
 simpl; lia_comp.
*discriminate.
*discriminate.
*rewrite map_length in IH.
 apply IH; tauto.
*apply IH; tauto.
Defined.
Lemma free_var_context_length : forall (ctx : list TypeF) (ty : TypeF) (t : Term),
  ctx⊢t¦ty -> free_var t <= length ctx.
Proof.
intros ctx ty t Hderiv.
induction Hderiv as [ ctx ty | ctx ty n ty' Hderiv IH | ctx ty t1 ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx t ty Hderiv IH | ctx t ty ty' Hderiv IH ].
*rewrite free_var_leaf.
 simpl length; lia_comp.
*rewrite free_var_leaf in IH; rewrite free_var_leaf.
 simpl length; lia_comp.
*rewrite free_var_bind.
 simpl length in IH; lia_comp.
*rewrite free_var_node. lia_comp.
*rewrite map_length in IH; assumption.
*assumption.
Defined.
(** In a given type context, a substitution is compatible with a
  context if any element of the subtitution is in the reducibility
  candidate associated to the corresponding type in the context *)
Inductive CompatSubst : (nat -> Term -> Prop) -> list TypeF -> list Term -> Prop :=
  | CompatNil : forall (t_ctx : nat -> Term -> Prop), CompatSubst t_ctx nil nil
  | CompatCons : forall (t_ctx : nat -> Term -> Prop) (ctx : list TypeF) (s : list Term) (ty : TypeF) (t : Term), CompatSubst t_ctx ctx s -> red_cand t_ctx ty t -> CompatSubst t_ctx (ty :: ctx) (t :: s).
Lemma compat_length : forall (t_ctx : nat -> Term -> Prop) (ctx : list TypeF) (s : list Term), CompatSubst t_ctx ctx s -> length ctx = length s.
Proof.
intros t_ctx ctx s Hcompat.
induction Hcompat as [ | t_ctx ctx s ty t _ IH ].
*reflexivity.
*simpl; rewrite IH; reflexivity.
Defined.
Lemma compat_id : forall (t_ctx : nat -> Term -> Prop) (ctx : list TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> CompatSubst t_ctx ctx (0…(length ctx)-1).
Proof.
intros t_ctx ctx Ht_ctx.
replace (length ctx) with (0 + length ctx)%nat by lia_comp.
generalize 0.
induction ctx as [ | ty ctx IH ]; intro n.
*rewrite var_nil by (simpl; lia_comp).
 apply CompatNil.
*rewrite var_cons by (simpl; lia_comp).
 apply CompatCons.
 +simpl length.
  replace (n + S (length ctx))%nat with (S n + length ctx)%nat by lia_comp.
  apply IH.
 +apply RedCandVar.
  apply red_cand_RedCand.
  assumption.
Defined.
(** If [t] has type [ty] in context [ctx], then for any
  type context [t_ctx] consisting of reducibility candidates,
  and for any substitution [s] compatible with [ctx] in [t_ctx],
  [t] is in the reducibility candidate associated to [ty] *)  
Lemma termf_red_cand : forall (t_ctx : nat -> Term -> Prop) (ctx : list TypeF) (s : list Term) (t : Term) (ty : TypeF),
  (forall (n : nat), RedCand (t_ctx n)) -> CompatSubst t_ctx ctx s -> ctx⊢t¦ty -> red_cand t_ctx ty (t[[0↦s]]).
Proof.
intros t_ctx ctx s t ty Ht_ctx Hcompat Hderiv.
revert t_ctx Ht_ctx s Hcompat.
induction Hderiv as [ ctx ty | ctx ty n ty' Hderiv IH | ctx ty t1 ty' Hderiv IH | ctx t ty ty' t' Hderiv1 IH1 Hderiv2 IH2 | ctx t ty Hderiv IH | ctx t ty ty' Hderiv IH ]; intros t_ctx Ht_ctx s Hcompat.
*destruct s.
 +inversion Hcompat.
 +inversion_clear Hcompat. simpl. assumption.
*destruct s.
 +inversion Hcompat.
 +inversion_clear Hcompat as [ | t_ctx' ctx' s' ty'' t' Hcompat' _ ].
  specialize (IH _ Ht_ctx _ Hcompat').
  rewrite substitute_list_leaf1 in IH by lia_comp.
  replace (n - 0) with n in IH by lia_comp.
  rewrite substitute_list_cons.
  rewrite substitute_list_leaf1 by lia_comp.
  replace ((S n) - 1) with n by lia_comp.
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
Defined.
(** In particular, any well-typed term is normalizing *)
Lemma termf_norm : forall (ctx : list TypeF) (t : Term) (ty : TypeF),
  ctx⊢t¦ty -> Normalizing t.
Proof.
intros ctx t ty Hderiv.
apply (@RedCand_Normalizing (red_cand (fun n => Normalizing) ty)).
*apply red_cand_RedCand.
 intro n; apply SNRedCand.
*rewrite <- (id_subst _ 0 (free_var_context_length Hderiv)).
 eapply termf_red_cand; [ | | exact Hderiv ].
 +intro n'; apply SNRedCand.
 +apply compat_id.
  intro n; apply SNRedCand.
Defined.
(** Moreover, being a normal form is a decidable property *)
Lemma normal_dec : forall (t : Term), (forall (t' : Term), ~ t ≻ t') + {t' : Term | t ≻ t'}.
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
Lemma normal_form : forall (t : Term), Normalizing t -> {t' : Term | t ≻* t' /\ forall t'', ~ t' ≻ t''}.
Proof.
intros t Hnorm.
induction Hnorm as [ t _ IH ].
case (normal_dec t); intro Hdec.
*exists t.
 split.
 +apply Refl.
 +assumption.
*destruct Hdec as [t' Hred ].
 destruct (IH _ Hred) as [ t'' IH' ]; clear IH.
 destruct IH' as [ Hred' Hnorm ].
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
  TermF ctx t ty -> {t' : Term | t ≻* t' /\ forall t'', ~ t' ≻ t''}.
Proof.
intros ctx t ty Hderiv.
apply normal_form.
eapply termf_norm; exact Hderiv.
Defined.

Unset Implicit Arguments.

Definition nf (ctx : list TypeF) (t : Term) (ty : TypeF) (p : TermF ctx t ty) : Term
  := match termf_normal_form p with exist _ u _ => u end.


Definition tm_id := (λ (# 0)).

Definition example : Term := tm_id @ (# 0).


(* as we can see, the reduction is stuck due to qed proofs in prop *)
(*
Eval compute in @nf cheat example cheat cheat.
Eval compute in @nf cheat (tm_id @ (tm_id @ tm_id) @ tm_id) cheat cheat.
*)
(* Require Extraction.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant length => "List.length".
Extract Inlined Constant map => "List.map".
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inlined Constant plus => "(+)".
Extract Inlined Constant max => "max".
Extraction "Normalization.ml" termf_normal_form. *)

Ltac auto_typing := repeat (econstructor; cbn).

Lemma omegaTypeF : nil ⊢ λ (#0@#0) ¦ ∀(&0⇒&0) ⇒ ∀(&0⇒&0).
Proof.
auto_typing.
change (∀(&0⇒&0)⇒∀(&0⇒&0)) with ((&0⇒&0)[0↦∀(&0⇒&0)]).
auto_typing.
Defined.

Definition church_nat := ∀ (&0 ⇒ (&0⇒&0) ⇒ &0).

Definition zero := λ λ #1.

Lemma zeroT Γ : Γ ⊢ zero ¦ church_nat.
Proof.
auto_typing.
Defined.
  
Definition succ := λ λ λ #0 @ (#2 @ #1 @ #0).

Lemma succT Γ : Γ ⊢ succ ¦ church_nat ⇒ church_nat.
Proof.
auto_typing.
change ((&0⇒(&0⇒&0)⇒&0)) with ((&0⇒(&0⇒&0)⇒&0)[0↦&0]).
auto_typing.
Defined.

Definition one := λ λ (# 0 @ # 1).

Lemma oneT Γ : Γ ⊢ one ¦ church_nat.
Proof.
auto_typing.
Defined.

Definition two := λ λ (# 0 @ (# 0 @ # 1)).

Lemma twoT Γ : Γ ⊢ one ¦ church_nat.
Proof.
auto_typing.
Defined.

Definition three := succ @ two.

Definition plus := λ (*n*) λ (*m*) (#1 @ #0 @ succ).

Lemma plusT Γ : Γ ⊢ plus ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 3 econstructor.
  2: eapply succT.
  auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Defined. 

Definition mult := λ (*n*) λ (*m*) (#1 @ zero @ (plus @ #0)).

Lemma multT Γ : Γ ⊢ mult ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 4 econstructor.
  3: apply plusT.
  2: apply zeroT.
  all: auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Defined. 

Definition exp := λ (*n*) λ (*m*) (#0 @ one @ (mult @ #1)).

Lemma expT Γ : Γ ⊢ exp ¦ church_nat ⇒ church_nat ⇒ church_nat.
Proof.
  unfold plus. do 4 econstructor.
  2: apply oneT. 
  2: apply multT. 
  all: auto_typing. 
  change (church_nat ⇒ (church_nat ⇒ church_nat) ⇒ church_nat) with ((&0⇒(&0⇒&0)⇒&0)[0↦church_nat]).
  auto_typing.
Defined. 

Definition four := mult @ two @ two.

Definition exp2 n := exp @ two @ n.

Ltac auto_typing_nat := repeat (first [apply succT | apply plusT | apply multT | apply expT | econstructor]; cbn).

Goal nf nil (succ @ zero) church_nat (ltac:(auto_typing_nat)) = one.
  Time lazy; reflexivity.
Abort.

Definition eight := exp2 three.

Lemma eightT : nil ⊢ eight ¦ church_nat.
auto_typing_nat.
Defined.

Definition eight' := plus @ four @ four.

Lemma eightT' : nil ⊢ eight' ¦ church_nat.
auto_typing_nat.
Defined.

Goal nf nil (exp2 two) church_nat (ltac:(auto_typing_nat)) = nf nil (plus @ two @ two) church_nat (ltac:(auto_typing_nat)) .
  Time lazy; reflexivity.
Abort.

(*
Goal nf nil (exp2 three) church_nat (ltac:(auto_typing_nat)) = nf nil (plus @ four @ four) church_nat (ltac:(auto_typing_nat)) .
  Fail Timeout 50 reflexivity.
Abort.
*)