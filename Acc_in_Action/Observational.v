Set Universe Polymorphism.

Inductive SFalse: SProp := .
Inductive STrue: SProp := tt.

Definition not (A : SProp) := forall (_ : A), SFalse.

Register STrue as core.True.type.
Register tt as core.True.I.
Register SFalse as core.False.type.


(* The observational equality *)

Cumulative Inductive Eq@{s;u} (A : Type@{s;u}) (a : A) : forall (b : A), SProp :=
| refl : Eq A a a.


Notation "a ~ b" := (Eq _ a b) (at level 50).
Arguments Eq {A} a _.
Arguments refl {A a} , [A] a.

Register Eq as core.eq.type.
Register refl as core.eq.refl.

(* Type casting *)


Instance Eq_Has_refl@{α;l} : Has_refl@{α SProp;l Set} (@Eq) :=
  fun A x => refl.

Instance Eq_Has_J_elim_SProp@{α;l} : Has_J@{α SProp SProp;l Set Set} (@Eq) _
  := @Eq_sind.

Hint Resolve Eq_Has_J_elim_SProp : rewrite_instances.

Instance Eq_Has_Leibniz_elim_SProp@{α;l} : Has_Leibniz@{α SProp SProp;l Set Set} (@Eq)
  := fun A x P t y e => @Eq_sind A x (fun x _ => P x) t y e.

Hint Resolve Eq_Has_Leibniz_elim_SProp : rewrite_instances.

Instance Eq_Has_Leibniz_r_elim_SProp@{α;l +} : Has_Leibniz_r@{α SProp SProp;l Set Set} (@Eq)
  := fun A x P t y e => @Eq_sind A x (fun x _ => P x) t y (sym@{α SProp;l Set} e).

Hint Resolve Eq_Has_Leibniz_r_elim_SProp : rewrite_instances.

Symbol cast@{α;u u' | u<u'} : forall (A B : Type@{α;u}), A ~ B -> A -> B.

Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

Instance Eq_Has_Leibniz_elim@{α β;l l' +} : Has_Leibniz@{α SProp β;l Set l'} (@Eq) :=
 { leibniz := fun A x P px y e => cast (P x) (P y) (ap P e) px}.

Hint Resolve Eq_Has_Leibniz_elim : rewrite_instances.

Instance Eq_Has_Leibniz_r_elim@{α β;l l' +} : Has_Leibniz_r@{α SProp β;l Set l'} (@Eq) :=
 { leibniz_r := fun A x P px y e => cast (P x) (P y) (ap P (sym e)) px}.

Hint Resolve Eq_Has_Leibniz_r_elim : rewrite_instances.

Definition Eq_apd@{sa sb; la lb lb' +}
    {A : Type@{sa;la}} {a} (P : forall b : A, a ~ b -> Type@{sb ; lb})
    (b : A) (e : a ~ b) : @Eq _ (P a refl) (P b e) :=
    J_eliminator _ a (fun b e => @Eq _ (P a refl) (P b e)) refl b e.

Instance Eq_Has_J_elim@{α β;l l' +} : Has_J@{α SProp β;l l l'} (@Eq) _ :=
  fun A a P t b e => cast (P a refl) (P b e) (Eq_apd@{α β ;l l' _ _} P b e) t.

Hint Resolve Eq_Has_J_elim : rewrite_instances.

(* SProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SProp *)

Definition cast_prop (A B : SProp) (e : @Eq SProp A B) (a : A) := Eq_sind SProp A (fun X _ => X) a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

(* We can use cast to derive large elimination principles for Eq *)

Section ObsEq.
  Sort s sP.
  Universe u uP.
  Variable A B : Type@{s;u}.

  Definition Eq_trans {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
    Eq_sind _ b (fun X _ => a ~ X) e c e'.

Definition Eq_sym {A : Type@{s;u}} {a b : A} (e : a ~ b) : b ~ a :=
  Eq_sind _ a (fun X _ => X ~ a) refl b e. 

Lemma Eq_sind_r : forall [A : Type@{s;u}] [x : A] (P : A -> SProp),
       P x -> forall [y : A], y ~ x -> P y.
Proof.
  intros. now destruct H0.
Qed. 

Definition ap (f : A -> B) {x y} (e : x ~ y) : f x ~ f y :=
  Eq_sind _ x (fun y _ => f x ~ f y) refl _ e.

Definition apd {a} (P : forall b : A, a ~ b -> Type@{sP;uP}) (b : A) (e : a ~ b) : (P a refl) ~ (P b e) :=
  Eq_sind _ a (fun b e => (P a refl) ~ (P b e)) refl b e.

Definition Eq_rect : forall (a : A) (P : forall b : A, Eq@{s;u} a b -> Type@{sP;uP}),
    P a refl@{_;u} -> forall (b : A) (e : Eq@{_;u} a b), P b e :=
  fun a P t b e => cast@{sP;uP _} (P a refl) (P b e) (apd P b e) t.

Definition Eq_rec := Eq_rect.
End ObsEq.

Notation "e @@@ f" := (Eq_trans e f) (at level 40, left associativity, only parsing).

Register Eq_Has_Leibniz_elim_SProp as core.eq.sind.
Register ap as core.eq.congr.
Register Eq_sind_r as core.eq.sind_r.

  (*
(* The Prop eliminator is an axiom.
   The observational equality should not be used with Prop anyway. *)
Axiom Eq_ind@{u} : forall (A : Type@{u}) (a : A) (P : forall b : A, Eq@{u} a b -> Prop),
    P a refl@{u} -> forall (b : A) (e : Eq@{u} a b), P b e.
*)
(** Definition of the observational equality on pi's *)

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

Lemma bool_disc : false ~ true -> SFalse.
Proof. 
  discriminate.
Qed.
