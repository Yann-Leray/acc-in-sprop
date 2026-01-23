Set Universe Polymorphism.

From SystemF Require Import Sigma sum Observational Arith.

Fixpoint map {A B} (f : A -> B) (l:list A) : list B :=
  match l with
    | nil => nil
    | cons a l => cons (f a) (map f l)
  end.

Lemma map_length {A' B'} (f : A' -> B') : forall l, length (map f l) ~ length l.
  induction l; cbn. 
  - reflexivity.
  - now apply ap.
Qed.

Infix "::" := cons (at level 60, right associativity).

Fixpoint nth {B} (n:nat) (l:list B) (default : B): B :=
    match n, l with
      | O, x :: l' => x
      | O, nil => default
      | S m, nil => default
      | S m, x :: l' => nth m l' default
    end.

Lemma map_nth {A' B'} (f : A' -> B'): forall l d n,
nth n (map f l) (f d) ~ f (nth n l d).
Proof.
  induction l; destruct n; cbn; intros; try reflexivity; eauto.
Qed.

Lemma nth_overflow {A'} : forall (l : list A') n d, length l <= n -> nth n l d ~ d.
Proof.
  induction l; destruct n; cbn; intros; try reflexivity.
  - inversion H.
  - eapply IHl. inversion H; eauto.
Qed. 

Lemma nth_indep {A'} : forall (l : list A') n d d', n < length l -> nth n l d ~ nth n l d'.
Proof.
  induction l; destruct n; cbn; intros; try reflexivity; inversion H; eauto. 
Qed. 

Fixpoint seq (start len:nat) : list nat :=
  match len with
    | 0 => nil
    | S len => start :: seq (S start) len
  end.

Lemma seq_nth : forall len start n d,
  n < len -> (nth n (seq start len) d) ~ (plus start n).
Proof.
  intro len; induction len as [|len IHlen]; intros start n d H.
  - inversion H.
  - simpl seq.
    destruct n; simpl.
    + now rewrite plus_zero.
    + inversion H. 
      now rewrite IHlen; [rewrite plus_commS | eauto].
Qed.

Lemma seq_length : forall len start, length (seq start len) ~ len.
  intro len; induction len; simpl; intros.
  + reflexivity.
  + apply ap, IHlen.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
map g (map f l) ~ map (fun x => g (f x)) l.
Proof.
  induction l; cbn.
  - reflexivity.
  - now eapply ap. 
Qed.

Lemma seq_shift : forall len start,
map S (seq start len) ~ seq (S start) len.
Proof.
  intro len; induction len as [|len IHlen]; simpl; try reflexivity.
  intros. now rewrite IHlen.
Qed.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a ~ g a) -> forall l, map f l ~ map g l.
Proof.
  induction l; cbn; try reflexivity. 
  rewrite H. now apply ap.
Qed.
