Require Import library.

(* This file postulates the ZF axioms in higher order logic (HOL), which has itself been embedded in
   the logic of Rocq (see library.v).
   The axioms are skolemised, meaning that we replace existential axioms with higher-order functions *)

(* Sort for sets *)
Parameter ZFSet : Set.

(* Membership relation *)
Parameter ZFin : ZFSet -> ZFSet -> SProp.
Notation "A ∈ B" := (ZFin A B) (at level 45, no associativity).
Notation "'∃' a '∈' A ',' P" := (exS ZFSet (fun x => x ∈ A ∧ (fun a => P) x)) (at level 100, a at level 44).
Notation "'∃!' a '∈' A ',' P" := (exU ZFSet (fun x => x ∈ A ∧ (fun a => P) x)) (at level 100, a at level 44).
Notation "'∀' a '∈' A ',' P" := (forall x : ZFSet, x ∈ A -> (fun a => P) x) (at level 100, a at level 44).

(* Subset relation *)
Definition ZFsub : ZFSet -> ZFSet -> SProp :=
  fun A B => forall (a : ZFSet), a ∈ A -> a ∈ B.
Notation "A ⊂ B" := (ZFsub A B) (at level 45, no associativity).

(* Extensionality axiom *)
Axiom ZFext : forall (A B : ZFSet), A ⊂ B -> B ⊂ A -> A ≡ B.

(* Skolemised empty set axiom *)
Parameter ZFempty : ZFSet.
Notation "∅" := ZFempty.
Axiom ZFinempty : ∀ a ∈ ∅, FalseS.

(* Skolemised comprehension axiom. In the usual first-order presentation of ZF, comprehension has to
   be formulated as an axiom scheme. Here, we are using a higher-order presentation, so we can use
   quantification over predicates. *)
Parameter ZFcomp : ZFSet -> (ZFSet -> SProp) -> ZFSet.
Notation "'{' x 'ϵ' A '∣' F '}'" := (ZFcomp A (fun x => F)) (at level 0).
Axiom ZFincomp : forall (A : ZFSet) (φ : ZFSet -> SProp) (a : ZFSet), a ∈ { x ϵ A ∣ φ x } ↔ (a ∈ A) ∧ φ a.

(* Skolemised pairing axiom *)
Parameter ZFpairing : ZFSet -> ZFSet -> ZFSet.
Notation "'{' a ';' b '}'" := (ZFpairing a b) (at level 0).
Axiom ZFinpairing : forall (a b x : ZFSet), x ∈ { a ; b } ↔ x ≡ a ∨ x ≡ b.

(* Definition of singleton from pairing *)
Definition setSingl : ZFSet -> ZFSet :=
  fun a => { a ; a }.
Lemma inSetSingl (a : ZFSet) : forall x, x ∈ setSingl a ↔ x ≡ a.
Proof.
  intro x. split.
  - intro H. apply (ZFinpairing a a x) in H. now destruct H.
  - intro H. apply (sndS (ZFinpairing a a x)). now left.
Qed.

(* Skolemised union axiom *)
Parameter ZFunion : ZFSet -> ZFSet.
Notation "⋃" := ZFunion.
Axiom ZFinunion : forall (A a : ZFSet), a ∈ ⋃ A ↔ ∃ x ∈ A, a ∈ x.

(* Skolemised replacement axiom. Here again, we use a higher-order axiom instead of an axiom scheme.
   TODO: we don't really need replacement since we have Grothendieck universes... *)
Parameter ZFreplacement : ZFSet -> (ZFSet -> ZFSet -> SProp) -> ZFSet.
Notation "'{' y '∥' P '∥' x 'ϵ' A '}'" := (ZFreplacement A (fun x y => P)) (at level 0).
Axiom ZFinreplacement : forall (A : ZFSet) (φ : ZFSet -> ZFSet -> SProp) (b : ZFSet),
    (∀ x ∈ A, exU ZFSet (φ x)) -> (b ∈ { y ∥ φ x y ∥ x ϵ A } ↔ ∃ x ∈ A, φ x b).

(* Skolemised infinity axiom.
   TODO: this formulation allows induction over ω for all HOL predicates. This is unusual: the
   traditional method consists in postulating a set closed under successor, and then carving ω
   out of it with comprehension.
   *)
Parameter ZFinfinity : ZFSet.
Definition ω := ZFinfinity.
Definition ZFsuc : ZFSet -> ZFSet := fun x => { x ; setSingl x }.
Axiom ZFininfinity : forall (x : ZFSet), x ∈ ω ↔ forall (P : ZFSet -> SProp), P ∅ -> (forall x, P x -> P (ZFsuc x)) -> P x.

(* Skolemised powerset axiom *)
Parameter ZFpower : ZFSet -> ZFSet.
Definition 𝒫 := ZFpower.
Axiom ZFinpower : forall (A x : ZFSet), x ∈ 𝒫 A ↔ x ⊂ A.

(* Russell's definite description operator
   TODO: I think that it is conservative over IZF, but I am not 100% sure *)
Parameter ZFdescr : ZFSet -> ZFSet.
Definition ι := ZFdescr.
Axiom ZFindescr : forall (A : ZFSet), (exU ZFSet (fun a => a ∈ A)) -> ι A ∈ A.

(* countably many Grothendieck universes *)
Parameter ZFuniv : nat -> ZFSet.
Definition 𝕍 := ZFuniv.
Axiom ZFuniv_uncountable : forall n, ω ∈ 𝕍 n.
Axiom ZFuniv_hierarchy : forall n, 𝕍 n ∈ 𝕍 (S n).
Axiom ZFuniv_trans : forall n x y, x ∈ y -> y ∈ 𝕍 n -> x ∈ 𝕍 n.
Axiom ZFuniv_pair : forall n x y, x ∈ 𝕍 n -> y ∈ 𝕍 n -> { x ; y } ∈ 𝕍 n.
Axiom ZFuniv_power : forall n x, x ∈ 𝕍 n -> 𝒫 x ∈ 𝕍 n.
Axiom ZFuniv_union : forall n I (φ : ZFSet -> ZFSet -> SProp), I ∈ 𝕍 n -> (∀ i ∈ I, ∃! x ∈ 𝕍 n, φ i x)
                                                               -> ⋃ { x ϵ 𝕍 n ∣ ∃ i ∈ I, φ i x } ∈ 𝕍 n.
Axiom ZFuniv_descr : forall n x, x ⊂ 𝕍 n -> ι x ∈ 𝕍 n.
