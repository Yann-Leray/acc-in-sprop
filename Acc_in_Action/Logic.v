(** * Equivalences

  Some definitions and lemmas about equivalences *)

Set Universe Polymorphism.

From SystemF Require Import Sigma.

Reserved Notation "X <-> Y" (at level 95, no associativity).
Reserved Notation "X <~> Y" (at level 95, no associativity).
Reserved Notation "X <~~> Y" (at level 95, no associativity).


Definition siff (A B : SProp) : SProp := prod (A -> B) (B -> A).
 
Reserved Notation "X <--> Y" (at level 95, no associativity).
Infix "<-->" := siff.


Lemma iff_forall : forall (A : Type) (P Q R : (A -> SProp) -> SProp),
  (forall X, R X -> (P X <--> Q X))
    -> ((forall X, R X -> P X) <--> (forall X, R X -> Q X)).
Proof.
intros A P Q R H.
split; intros H' X HX; apply H; try apply H'; apply HX.
Qed.
Definition iffE {A : Type} (X Y : A -> SProp) : SProp :=
  forall (a : A), siff (X a) (Y a).
Infix "<~>" := iffE.
Lemma iffE_trans : forall (A : Type) (X Y Z : A -> SProp),
  (X <~> Y) -> (Y <~> Z) -> (X <~> Z).
Proof.
simpl.
intros A X Y Z Heq1 Heq2 t.
split; intro H.
apply Heq2; apply Heq1; assumption.
apply Heq1; apply Heq2; assumption.
Qed.
Lemma iffE_forall : forall (A : Type) (P Q P' Q' : A -> SProp),
  (P <~> Q)
    -> (P' <~> Q')
    -> ((forall X, P X -> P' X) <--> (forall X, Q X -> Q' X)).
Proof.
intros A P Q P' Q' H H'.
split; intros H0 X HX; apply H'; apply H0; apply H; apply HX.
Qed.
Definition iffE2 {A B : Type} (X Y : A -> B -> SProp) :=
  forall (a : A), (X a <~> Y a).
Infix "<~~>" := iffE2.
Lemma iffE2_trans : forall (A B : Type) (X Y Z : A -> B -> SProp),
  (X<~~> Y) -> (Y <~~> Z) -> (X <~~> Z).
Proof.
simpl.
intros A B X Y Z Heq1 Heq2 n t.
split; intro H.
apply Heq2; apply Heq1; assumption.
apply Heq1; apply Heq2; assumption.
Qed.