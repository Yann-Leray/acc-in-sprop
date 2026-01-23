(* Our model construction is supposed to take place in ZF set theory, which is a set of axioms that
   can be put on top of first order logic (FOL). However, we certainly do not want to do a deep
   embedding of FOL in the logic of Rocq!
   Instead, we will use a shallow embedding of HOL into Rocq's logic (by carefully avoiding the use
   of dependent types and universes) and then postulate the skolemised axioms of ZF in HOL. This
   file does the shallow embedding of HOL into Rocq.

   - We use [SProp] as our type of truth values (note that we postulate classical logic, so
     [SProp] becomes isomorphic to [bool]).
   - Dependent function types are not allowed, only universal quantifiers are allowed
     (i.e., we can write [forall] only when writing an inhabitant of [SProp]).
   - We allow prenex polymorphism over [Set], but we do not use universes otherwise.
   - Inductive types are used to simulate the logical connectives [∧] [∨] [⊤] [⊥] [∃] [=].
   - Large elimination is disallowed thanks to them living in [SProp].
 *)

(* Conjunction of truth values *)
Inductive andS (A : SProp) (B : SProp) : SProp :=
| mkAndS : A -> B -> andS A B.
Arguments mkAndS {_} {_}.
Notation "A ∧ B" := (andS A B) (at level 80, right associativity).

Lemma fstS {A B} : A ∧ B -> A.
Proof.
  intros [HA HB]. exact HA.
Qed.

Lemma sndS {A B} : A ∧ B -> B.
Proof.
  intros [HA HB]. exact HB.
Qed.

(* Disjunction of truth values *)
Inductive orS (A B : SProp) : SProp :=
| orS_introl : A -> orS A B
| orS_intror : B -> orS A B.
Notation "A ∨ B" := (orS A B) (at level 85, right associativity).

Inductive FalseS : SProp :=.

Inductive TrueS : SProp := ttS.

Definition notS : SProp -> SProp := fun A => A -> FalseS.
Notation "¬ A" := (notS A) (at level 75, right associativity).

Definition bi_impl : SProp -> SProp -> SProp := fun A B => (A -> B) ∧ (B -> A).
Notation "A ↔ B" := (bi_impl A B) (at level 95, no associativity).

Inductive eqS (A : Set) (a : A) : A -> SProp :=
| eqS_refl : eqS A a a.
Arguments eqS {_}.
Arguments eqS_refl {_}.
Notation "x ≡ y" := (eqS x y) (at level 70, no associativity).

Definition transpS {A : Set} (P : A -> SProp) {a b : A} : a ≡ b -> P a -> P b.
Proof.
  intros e p. exact (eqS_sind A a (fun b _ => P b) p b e).
Qed.

Lemma transp2S {A B : Set} (P : A -> B -> SProp) {a a' : A} {b b' : B} : a ≡ a' -> b ≡ b' -> P a b -> P a' b'.
  intros ea eb t. destruct ea. destruct eb. exact t.
Qed.

Lemma fequal {A B : Set} (f : A -> B) {a a' : A} : a ≡ a' -> f a ≡ f a'.
  intro e. destruct e. reflexivity.
Qed.

Lemma fequal2 {A B C : Set} (f : A -> B -> C) {a a' : A} {b b' : B} : a ≡ a' -> b ≡ b' -> f a b ≡ f a' b'.
  intros e1 e2. destruct e1. destruct e2. reflexivity.
Qed.

Lemma fequal3 {A B C D : Set} (f : A -> B -> C -> D) {a a' : A} {b b' : B} {c c' : C} : a ≡ a' -> b ≡ b' -> c ≡ c' -> f a b c ≡ f a' b' c'.
  intros e1 e2 e3. destruct e1. destruct e2. destruct e3. reflexivity.
Qed.

Lemma sym {A : Set} {a b : A} : a ≡ b -> b ≡ a.
Proof.
  intro e. exact (eqS_sind A a (fun b _ => b ≡ a) (eqS_refl a) b e).
Qed.

Lemma trans {A : Set} {a b c : A} : a ≡ b -> b ≡ c -> a ≡ c.
Proof.
  intros e1 e2. apply (transpS (fun c => a ≡ c) e2). exact e1.
Qed.

Inductive exS (A : Set) (B : A -> SProp) : SProp :=
| exS_intro : forall x : A, B x -> exS A B.

Definition uniqueS {A : Set} (P : A -> SProp) (x : A) :=
  P x ∧ forall (x':A), P x' -> x ≡ x'.

Definition exU (A : Set) (B : A -> SProp) : SProp := exS A (uniqueS B).


