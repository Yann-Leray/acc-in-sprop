Set Universe Polymorphism.


(* In this file, we work internally in the type theory defined in TypingP. 
   However, we will only need to postulate the conversions associated 
   with cast propositionally, allowing us to avoid declaring rewrite rules. *)


(* --- START OF THE DEF OF OBS EQ --- *)

Inductive obseq@{u} (A : Type@{u}) (a : A) : forall (b : A), SProp :=
| obseq_refl : obseq A a a.
Notation "a ~ b" := (obseq _ a b) (at level 50).
Arguments obseq {A} a _.
Arguments obseq_refl {A a} , [A] a.

Definition obseq_trans {A : Type} {a b c : A} (e : a ~ b) (e' : b ~ c) : a ~ c :=
  obseq_sind _ b (fun X _ => a ~ X) e c e'.
Notation "e @@@ f" := (obseq_trans e f) (at level 40, left associativity, only parsing).

Definition obseq_sym {A : Type} {a b : A} (e : a ~ b) : b ~ a :=
  obseq_sind _ a (fun X _ => X ~ a) obseq_refl b e.

(* Type casting *)

Axiom cast@{u v} : forall (A B : Type@{u}), @obseq@{v} Type@{u} A B -> A -> B.
Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

(* SProp casting *)
(* We do not want to use sort polymorphism for cast, to avoid useless (and potentially looping)
   computations in SProp *)

Definition cast_prop (A B : SProp) (e : @obseq SProp A B) (a : A) := obseq_sind SProp A (fun X _ => X) a B e.
Notation "e #% a" := (cast_prop _ _ e a) (at level 40, only parsing).

Axiom cast_refl : forall A e t, cast A A e t ~ t.

(* We can use cast to derive large elimination principles for obseq *)

Definition ap {A B} (f : A -> B) {x y} (e : x ~ y) : f x ~ f y :=
  obseq_sind _ x (fun y _ => f x ~ f y) obseq_refl _ e.

Definition apd {A} {a} (P : forall b : A, a ~ b -> Type) (b : A) (e : a ~ b) : (P a obseq_refl) ~ (P b e) :=
  obseq_sind _ a (fun b e => (P a obseq_refl) ~ (P b e)) obseq_refl b e.

Definition obseq_rect : forall (A : Type) (a : A) (P : forall b : A, obseq a b -> Type),
    P a obseq_refl -> forall (b : A) (e : obseq a b), P b e :=
  fun A a P t b e => cast (P a obseq_refl) (P b e) (apd P b e) t.

Definition obseq_rec : forall (A : Type) (a : A) (P : forall b : A, obseq a b -> Set),
    P a obseq_refl -> forall (b : A) (e : obseq a b), P b e :=
  fun A a P t b e => cast (P a obseq_refl) (P b e) (apd P b e) t.

(** Definition of the observational equality on pi's *)

Axiom obseq_forall_1@{u v +} : 
    forall 
        {A A' : Type@{u}} 
        {B : A -> Type@{v}} {B' : A' -> Type@{v}}, 
        (forall (x : A), B x) ~ (forall (x : A'), B' x) -> 
        A' ~ A.

Parameter obseq_forall_2@{u v+} : 
    forall 
        {A A' : Type@{u}} {B : A -> Type@{v}} {B' : A' -> Type@{v}}
        (e : (forall (x : A), B x) ~ (forall (x : A'), B' x))
        (x : A'), 
        (B (obseq_forall_1 e # x)) ~ (B' x).

Axiom obseq_forall_1_sprop : 
    forall 
        {A A' : SProp} 
        {B : A -> Type} {B' : A' -> Type}, 
        (forall (x : A), B x) ~ (forall (x : A'), B' x) -> 
        A' ~ A.

Parameter obseq_forall_2_sprop : 
    forall 
        {A A' : SProp} {B : A -> Type} {B' : A' -> Type}
        (e : (forall (x : A), B x) ~ (forall (x : A'), B' x))
        (x : A'), 
        (B (obseq_forall_1_sprop e #% x)) ~ (B' x).

Parameter funext : forall {A B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.


Parameter funext_sprop : forall {A : SProp} {B} (f g : forall (x : A), B x), (forall (x : A), f x ~ g x) -> f ~ g.

Axiom cast_pi : forall A B A' B' e f, 
    cast (forall (x : A), B x) (forall (x : A'), B' x) e f 
    ~ fun (x : A') => cast (B (cast A' A (obseq_forall_1 e) x))
                            (B' x)
                            (obseq_forall_2 e x)
                            (f (cast A' A (obseq_forall_1 e) x)).


Axiom cast_pi_sprop : forall A B A' B' e f, 
    cast (forall (x : A), B x) (forall (x : A'), B' x) e f 
    ~ fun (x : A') => cast (B (cast_prop A' A (obseq_forall_1_sprop e) x))
                            (B' x)
                            (obseq_forall_2_sprop e x)
                            (f (cast_prop A' A (obseq_forall_1_sprop e) x)).                    

Parameter propext : forall {A B : SProp}, (A -> B) -> (B -> A) -> A ~ B.

(* --- END OF THE DEF OF OBS EQ --- *)

(* postulating Acc *)
Axiom Acc : forall (A : Type) (R : A -> A -> SProp) (a : A), SProp.

Axiom acc_in : forall A R a (f : forall y, R a y -> Acc A R y), Acc A R a.
Axiom acc_inv : forall A R a, Acc A R a -> forall b, R a b -> Acc A R b.
Axiom acc_el : forall A R (P : A -> Type) (p : forall (a : A) (ϵf : forall y : A, R a y -> P y), P a) (y : A) (r : Acc A R y), P y.
Axiom acc_el_prop : forall A R (P : A -> SProp) (p : forall (a : A) (ϵf : forall y : A, R a y -> P y), P a) (y : A) (r : Acc A R y), P y.
(* end of Acc *)

(* Constructing Sigmas *)
Definition Σ (A : SProp) (B : A -> SProp) : SProp := 
    forall P, (forall a:A, B a -> P) -> P.

Definition fst {A B}: Σ A B -> A := 
    fun f => f A (fun a b => a).

Definition snd {A B}: forall (x : Σ A B), B (fst x) := 
    fun f => f (B (fst f)) (fun a b => b).

Definition mkΣ {A B} (a : A) (b : B a) : Σ A B := 
    fun P f => f a b.

(* the heterogeneous equality at sort Type *)
Definition heq_ty (A B : Type) (a : A) (b : B) := 
    Σ (A ~ B) (fun eq_ty => (eq_ty # a) ~ b).

Notation "a == b" := (heq_ty _ _ a b) (at level 90).


Inductive True : SProp := I.

(* the heterogeneous equality at sort SProp *)
Definition heq_prop (A B : SProp) (a : A) (b : B) : SProp := True.

Notation "a ~~ b" := (heq_prop _ _ a b) (at level 90).



Lemma homo_to_hetero {A : Type} {a b : A} (e : a ~ b) : a == b.
Proof.
    unshelve eapply mkΣ. eapply obseq_refl. 
    eapply obseq_trans. eapply cast_refl. eapply e.
Qed.

Lemma hetero_to_homo {A : Type} {a b : A} (e : a == b) : a ~ b.
Proof.
    eapply fst in e as e1. pose proof (e2 := snd e).
    destruct e1. destruct e2. eapply obseq_sym. eapply cast_refl.
Qed.

Lemma hetero_to_type_eq {A B : Type} {a : A} {b : B} (e : a == b) : A == B.
Proof. 
    eapply fst in e as e1. eapply homo_to_hetero. assumption. 
Qed.

(* auxiliary lemmas *)

Lemma ap' {A B} (f g : forall x : A, B x) (t : A): f ~ g -> f t ~ g t.
Proof.
    intros. destruct H. eapply obseq_refl.
Qed.


Lemma ap_sprop' {A : SProp} {B} (f g : forall x : A, B x) (t : A): f ~ g -> f t ~ g t.
Proof.
    intros. destruct H. eapply obseq_refl.
Qed.


(* -- heq_refl -- *)

Lemma heq_ty_refl {A : Type} (a : A) : a == a. 
Proof.
    unfold heq_ty. unshelve eapply mkΣ.
    - eapply obseq_refl.
    - eapply cast_refl.
Qed.

Lemma heq_prop_refl {A : SProp} (a : A) : a ~~ a.
Proof.
    econstructor.
Qed.

(* -- heq_sym -- *)

Lemma heq_ty_sym {A B : Type} {a : A} {b : B} (e : a == b) : b == a. 
Proof.
    unshelve eapply mkΣ.
    - eapply obseq_sym. eapply fst in e. assumption.
    - unfold heq_ty in e. eapply fst in e as e1. 
      pose proof (e2 := snd e). simpl in e2.
      destruct e1. destruct e2. eapply obseq_trans.
      eapply cast_refl.
      eapply cast_refl.
Qed.

Lemma heq_prop_sym {A B : SProp} {a : A} {b : B} (e : a ~~ b) : b ~~ a. 
Proof.
    econstructor.
Qed.

(* -- heq_trans -- *)

Lemma heq_ty_trans {A B C} {a : A} {b : B} {c : C} (p : a == b) (q : b == c) : a == c.
Proof.
    eapply fst in p as p1. pose proof (p2 := snd p).
    eapply fst in q as q1. pose proof (q2 := snd q). simpl in p2,q2.
    destruct p1. destruct q1. destruct q2. destruct p2.
    unshelve eapply mkΣ. eapply obseq_refl.
    eapply obseq_sym. eapply cast_refl.
Qed.

Lemma heq_prop_trans {A B C} {a : A} {b : B} {c : C} (p : a ~~ b) (q : b ~~ c) : a ~~ c.
Proof.
    econstructor.
Qed.

(* -- heq_cast -- *)

Lemma heq_ty_cast {A B} {e : A ~ B} {a} : a == (e # a).
Proof.
    destruct e. 
    eapply homo_to_hetero, obseq_sym, cast_refl.
Qed.

Lemma heq_prop_cast {A B} {e : A ~ B} {a} : a ~~ (e #% a).
Proof.
    econstructor.
Qed.


(* -- heq_app -- *)

Lemma heq_ty_ty_app : forall {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} {t : A1} {u : A2} (p : f == g) (q : t == u), (f t) == (g u).
Proof.  
    intros.
    eapply fst in p as p1. pose proof (p2 := snd p).
    eapply fst in q as q1. pose proof (q2 := snd q). simpl in p2,q2.
    destruct q1. destruct q2.
    unshelve eapply heq_ty_trans.
    2:exact (g t).
    - unshelve eapply mkΣ.
      * pose (e := obseq_forall_2 p1 t). destruct e. eapply ap. eapply obseq_sym, cast_refl.
      * destruct p2. eapply obseq_trans.
        2:eapply ap', obseq_sym, cast_pi.
        simpl. eapply hetero_to_homo. 
        eapply heq_ty_trans. eapply heq_ty_sym, heq_ty_cast.
        eapply heq_ty_trans. 2:eapply heq_ty_cast.
        pose proof (e := cast_refl _ (obseq_forall_1 (fst p)) t).
        unshelve eapply (obseq_sind _ _ (fun t' _ => f t' == f (cast A1 A1 (obseq_forall_1 (fst p)) t)) _ _).
        2:eapply heq_ty_refl. eapply cast_refl.
    - unshelve eapply (obseq_sind _ _ (fun t' _ => g t' == g (cast A1 A1 (fst q) t)) _ _).
      2:eapply heq_ty_refl. eapply cast_refl.
Qed.

Lemma heq_prop_ty_app : forall {A1 A2 : SProp} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} {t : A1} {u : A2} (p : f == g) (q : t ~~ u), (f t) == (g u).
Proof.
    intros.
    eapply fst in p as p1. pose proof (p2 := snd p). simpl in p2.
    pose (e1 := obseq_forall_1_sprop p1). destruct e1.
    unshelve eapply mkΣ.
      * pose (e := obseq_forall_2_sprop p1 t). eapply e.
      * destruct p2. eapply obseq_trans.
        2:eapply ap_sprop', obseq_sym, cast_pi_sprop.
        reflexivity.
Qed.

Lemma heq_ty_prop_app : forall {A1 A2 : Type} {B1 : A1 -> SProp} {B2 : A2 -> SProp} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} {t : A1} {u : A2} (p : f ~~ g) (q : t == u), (f t) ~~ (g u).
Proof.
    intros.
    econstructor.
Qed.

Lemma heq_prop_prop_app : forall {A1 A2 : SProp} {B1 : A1 -> SProp} {B2 : A2 -> SProp} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} {t : A1} {u : A2} (p : f ~~ g) (q : t ~~ u), (f t) ~~ (g u).
Proof.
    intros. econstructor.
Qed.

(* more auxiliary lemmas *)

Definition heq_ty_ty_funext : forall {A : Type} {B1 B2 : A -> Type} {f : forall x : A, B1 x} {g : forall x : A, B2 x} (p : forall x, f x == g x), f == g.
Proof.
    intros. unshelve eapply mkΣ.
    - eapply (ap (fun B => forall x : A, B x)). 
      eapply funext. intros. pose proof (px := p x).
      pose (px1 := fst px). assumption.
    - eapply funext. intros.
      pose proof (px := p x).
      pose (px1 := fst px). pose (px2 := snd px). simpl in px2.
      destruct px2. eapply obseq_trans.
      eapply ap'. eapply cast_pi. simpl.
      eapply hetero_to_homo.
      eapply heq_ty_trans.
      eapply heq_ty_sym, heq_ty_cast.
      eapply heq_ty_trans. 2:eapply heq_ty_cast.
      eapply heq_ty_ty_app. eapply heq_ty_refl. eapply homo_to_hetero, cast_refl.
Qed.


Definition heq_sprop_ty_funext : forall {A : SProp} {B1 B2 : A -> Type} {f : forall x : A, B1 x} {g : forall x : A, B2 x} (p : forall x, f x == g x), f == g.
Proof.
    intros. unshelve eapply mkΣ.
    - eapply (ap (fun B => forall x : A, B x)). 
      eapply funext_sprop. intros. pose proof (px := p x).
      pose (px1 := fst px). assumption.
    - eapply funext_sprop. intros.
      pose proof (px := p x).
      pose (px1 := fst px). pose (px2 := snd px). simpl in px2.
      destruct px2. eapply obseq_trans.
      eapply ap_sprop'. eapply cast_pi_sprop. simpl.
      eapply hetero_to_homo.
      eapply heq_ty_trans.
      eapply heq_ty_sym. 
      eapply (@heq_ty_cast (B1 (cast_prop A A (obseq_forall_1_sprop (ap (fun B : A -> Type => forall x0 : A, B x0) (funext_sprop B1 B2 (fun x0 : A => fst (p x0))))) x)) (B2 x)).
      eapply heq_ty_trans. 2:eapply heq_ty_cast. eapply heq_ty_refl.
Qed.

Definition heq_sprop_sprop_funext : forall {A : SProp} {B1 B2 : A -> SProp} {f : forall x : A, B1 x} {g : forall x : A, B2 x} (p : forall x, f x ~~ g x), f ~~ g.
Proof.
    intros. econstructor.
Qed.

Definition heq_ty_sprop_funext : forall {A : Type} {B1 B2 : A -> SProp} {f : forall x : A, B1 x} {g : forall x : A, B2 x} (p : forall x, f x ~~ g x), f ~~ g.
Proof.
    intros. econstructor.
Qed.

Definition heq_ty_ty_funext' {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f : forall x : A1, B1 x} {g : forall x : A2, B2 x} (e : A1 ~ A2) (p : forall x, f x == g (e # x)) : f == g.   
Proof.
    destruct e.
    eapply heq_ty_ty_funext.
    intros.
    eapply heq_ty_trans.
    exact (p x).
    eapply heq_ty_ty_app. eapply heq_ty_refl. eapply homo_to_hetero, cast_refl.
Qed.

(* -- heq_pi -- *)

Lemma heq_ty_ty_pi {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} (e1 : A1 == A2) (e2 : forall x1 x2, x1 == x2 -> B1 x1 == B2 x2) 
    : (forall x : A1, B1 x) == (forall x : A2, B2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1. 
    eapply homo_to_hetero.
    eapply (ap (fun B => forall x : A1, B x)).
    eapply funext. intros.
    eapply hetero_to_homo.
    eapply e2. eapply heq_ty_refl.
Qed.


Lemma heq_sprop_ty_pi {A1 A2 : SProp} {B1 : A1 -> Type} {B2 : A2 -> Type} (e1 : A1 == A2) (e2 : forall x1 x2, x1 ~~ x2 -> B1 x1 == B2 x2) 
    : (forall x : A1, B1 x) == (forall x : A2, B2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1. 
    eapply homo_to_hetero.
    eapply (ap (fun B => forall x : A1, B x)).
    eapply funext_sprop. intros.
    eapply hetero_to_homo.
    eapply e2. econstructor.
Qed.

Lemma heq_ty_sprop_pi {A1 A2 : Type} {B1 : A1 -> SProp} {B2 : A2 -> SProp} (e1 : A1 == A2) (e2 : forall x1 x2, x1 == x2 -> B1 x1 == B2 x2) 
    : (forall x : A1, B1 x) == (forall x : A2, B2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1. 
    eapply homo_to_hetero.
    eapply (ap (fun B => forall x : A1, B x)).
    eapply funext. intros.
    eapply hetero_to_homo.
    eapply e2. eapply heq_ty_refl.
Qed.

Lemma heq_sprop_sprop_pi {A1 A2 : SProp} {B1 : A1 -> SProp} {B2 : A2 -> SProp} (e1 : A1 == A2) (e2 : forall x1 x2, x1 ~~ x2 -> B1 x1 == B2 x2) 
    : (forall x : A1, B1 x) == (forall x : A2, B2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1. 
    eapply homo_to_hetero.
    eapply (ap (fun B => forall x : A1, B x)).
    eapply funext_sprop. intros.
    eapply hetero_to_homo.
    eapply e2. econstructor.
Qed.

(* -- heq_lam -- *)

Lemma heq_ty_ty_lam {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f1 : forall x : A1, B1 x} {f2 : forall x : A2, B2 x} 
    (e1 : A1 == A2) (e2 : forall x1 x2, x1 == x2 -> f1 x1 == f2 x2) 
    : (fun x => f1 x) == (fun x => f2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1.
    eapply heq_ty_ty_funext. intros.
    eapply e2. eapply heq_ty_refl.
Qed.


Lemma heq_sprop_ty_lam {A1 A2 : SProp} {B1 : A1 -> Type} {B2 : A2 -> Type} 
    {f1 : forall x : A1, B1 x} {f2 : forall x : A2, B2 x} 
    (e1 : A1 == A2) (e2 : forall x1 x2, x1 ~~ x2 -> f1 x1 == f2 x2) 
    : (fun x => f1 x) == (fun x => f2 x).
Proof.
    eapply hetero_to_homo in e1. destruct e1.
    eapply heq_sprop_ty_funext. intros.
    eapply e2. econstructor.
Qed.

Lemma heq_ty_sprop_lam {A1 A2 : Type} {B1 : A1 -> SProp} {B2 : A2 -> SProp} 
    {f1 : forall x : A1, B1 x} {f2 : forall x : A2, B2 x} 
    (e1 : A1 == A2) (e2 : forall x1 x2, x1 == x2 -> f1 x1 ~~ f2 x2) 
    : (fun x => f1 x) ~~ (fun x => f2 x).
Proof.
    intros. econstructor.
Qed.

Lemma heq_sprop_sprop_lam {A1 A2 : SProp} {B1 : A1 -> SProp} {B2 : A2 -> SProp} 
    {f1 : forall x : A1, B1 x} {f2 : forall x : A2, B2 x} 
    (e1 : A1 == A2) (e2 : forall x1 x2, x1 ~~ x2 -> f1 x1 ~~ f2 x2) 
    : (fun x => f1 x) ~~ (fun x => f2 x).
Proof.
    intros. econstructor.
Qed.

(* -- heq_obseq -- *)

Lemma heq_obseq {A1 A2 : Type} {a1 b1 : A1} {a2 b2 : A2} 
    (e2 : a1 == a2) (e3 : b1 == b2) : (@obseq A1 a1 b1) == (@obseq A2 a2 b2).
Proof.
    pose proof (e21 := fst e2). destruct e21.
    eapply hetero_to_homo in e2, e3. destruct e2, e3.
    eapply heq_ty_refl.
Qed.

(* -- heq_succ -- *)

Lemma heq_succ n m : n == m -> S n == S m.
Proof.
    intros. eapply hetero_to_homo in H. destruct H. eapply heq_ty_refl.
Qed.

(* -- heq_natrec -- *)

Lemma heq_ty_natrec {P1 P2 : nat -> Type} {pzero1 : P1 O} {pzero2 : P2 O} 
        {psucc1 : forall x : nat, P1 x -> P1 (S x)} {psucc2 : forall x : nat, P2 x -> P2 (S x)} {n1 n2}
        (e1 : forall x1 x2, x1 == x2 -> P1 x1 == P2 x2) (e2 : pzero1 == pzero2) 
        (e3 : forall x1 x2 p1 p2, x1 == x2 -> p1 == p2 -> psucc1 x1 p1 == psucc2 x2 p2) 
        (e4 : n1 == n2) : (@nat_rect P1 pzero1 psucc1 n1) == (@nat_rect P2 pzero2 psucc2 n2).
Proof.
    eapply heq_ty_ty_app; eauto.
    eapply (@heq_ty_ty_app _ _ _ _ (nat_rect P1 pzero1) (nat_rect P2 pzero2)).
    eapply (@heq_ty_ty_app _ _ _ _ (nat_rect P1) (nat_rect P2)).
    eapply (@heq_ty_ty_app _ _ _ _ nat_rect nat_rect).
    eapply heq_ty_refl.
    eapply heq_ty_ty_funext. intros. eapply (e1 x x). eapply heq_ty_refl.
    eapply e2.
    eapply heq_ty_ty_funext. intros.
    unshelve eapply heq_ty_ty_funext'.
    2:{ intros. eapply (e3 x x x0 _). eapply heq_ty_refl. eapply heq_ty_cast. }
    eapply hetero_to_homo. eapply e1. eapply heq_ty_refl. 
Qed.

Lemma heq_sprop_natrec {P1 P2 : nat -> SProp} {pzero1 : P1 O} {pzero2 : P2 O} 
        {psucc1 : forall x : nat, P1 x -> P1 (S x)} {psucc2 : forall x : nat, P2 x -> P2 (S x)} {n1 n2}
        (e1 : forall x1 x2, x1 == x2 -> P1 x1 == P2 x2) (e2 : pzero1 ~~ pzero2) 
        (e3 : forall x1 x2 p1 p2, x1 == x2 -> p1 ~~ p2 -> psucc1 x1 p1 ~~ psucc2 x2 p2) 
        (e4 : n1 == n2) : (@nat_sind P1 pzero1 psucc1 n1) ~~ (@nat_sind P2 pzero2 psucc2 n2).
Proof.
    econstructor.
Qed.

(* -- heq_cast' -- *)

Lemma heq_ty_cast' {A1 A2 B1 B2} (e1 : A1 ~ B1) (e2 : A2 ~ B2) (a1 : A1) (a2 : A2) (e : a1 == a2) : (e1 # a1) == (e2 # a2).
Proof.
    destruct e1. destruct e2. 
    pose proof (e1 := fst e). destruct e1.
    eapply heq_ty_trans. eapply heq_ty_trans.
    2:exact e.
    eapply heq_ty_sym. eapply (@heq_ty_cast _ _ obseq_refl a1).
    eapply heq_ty_cast.
Qed.

Lemma heq_prop_cast' {A1 A2 B1 B2 : SProp} (e1 : A1 ~ B1) (e2 : A2 ~ B2) (a1 : A1) (a2 : A2) (e : a1 ~~ a2) : (e1 #% a1) ~~ (e2 #% a2).
Proof.
    econstructor.
Qed.

(* -- heq_acc -- *)

Lemma heq_acc {A1 A2 R1 R2 a1 a2} 
        (e1 : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> R1 x1 y1 == R2 x2 y2) 
        (e2 : a1 == a2) 
        : (Acc A1 R1 a1) == (Acc A2 R2 a2).
Proof.
    pose proof (e21 := fst e2). destruct e21.
    eapply (@heq_ty_ty_app _ _ _ _ (Acc A1 R1) (Acc A1 R2)).
    2:assumption.
    eapply (@heq_ty_ty_app _ _ _ _ (Acc A1) (Acc A1)).
    eapply heq_ty_refl.
    eapply heq_ty_ty_funext. intros.
    eapply heq_ty_ty_funext. intros.
    eapply e1; eauto using heq_ty_refl.
Qed.

(* -- heq_acc_el -- *)

Lemma heq_ty_acc_el {A1 A2 R1 R2 a1 a2 P1 P2 p1 p2 q1 q2}
    (e0 : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> R1 x1 y1 == R2 x2 y2) 
    (e1 : forall x1 x2, x1 == x2 -> P1 x1 == P2 x2)
    (e2 : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> p1 x1 y1 == p2 x2 y2)
    (e3 : a1 == a2)
    : (acc_el A1 R1 P1 p1 a1 q1) == (acc_el A2 R2 P2 p2 a2 q2).
Proof.
    pose proof (e31 := fst e3). destruct e31.
    eapply (@heq_prop_ty_app _ _ _ _ (acc_el A1 R1 P1 p1 a1) (acc_el A1 R2 P2 p2 a2)). 
    2:econstructor.
    eapply (@heq_ty_ty_app _ _ _ _ (acc_el A1 R1 P1 p1) (acc_el A1 R2 P2 p2)).
    2:assumption.
    eapply (@heq_ty_ty_app _ _ _ _ (acc_el A1 R1 P1) (acc_el A1 R2 P2)).
    eapply (@heq_ty_ty_app _ _ _ _ (acc_el A1 R1) (acc_el A1 R2)).
    eapply (@heq_ty_ty_app _ _ _ _ (acc_el A1) (acc_el A1)).
    eapply heq_ty_refl.
    eapply heq_ty_ty_funext. intros.
    eapply heq_ty_ty_funext. intros.
    eapply e0; eauto using heq_ty_refl.
    eapply heq_ty_ty_funext. intros. eapply e1; eauto using heq_ty_refl.
    eapply heq_ty_ty_funext. intros.
    unshelve eapply heq_ty_ty_funext'. 
    2:{intros.
    eapply e2; eauto using heq_ty_refl.
    eapply heq_ty_cast. }
    eapply (ap (fun B => forall x : A1, B x)).
    eapply hetero_to_homo.
    eapply heq_ty_ty_funext.
    intros.
    pose proof (e0' := e0 x x (heq_ty_refl _) x0 x0 (heq_ty_refl _)). 
    eapply hetero_to_homo in e0'. destruct e0'.
    pose proof (e1' := e1 x0 x0 (heq_ty_refl _)).
    eapply hetero_to_homo in e1'. destruct e1'.
    eapply heq_ty_refl.
Qed.

Lemma heq_prop_acc_el {A1 A2 R1 R2 a1 a2} {P1 : A1 -> SProp} {P2 : A2 -> SProp} {p1 p2 q1 q2}
    (e0 : forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> R1 x1 y1 == R2 x2 y2) 
    (e1 : forall x1 x2, x1 == x2 -> P1 x1 == P2 x2)
    (e2 : forall x1 x2, x1 == x2 -> forall y1 y2, y1 ~~ y2 -> p1 x1 y1 ~~ p2 x2 y2)
    : (acc_el_prop A1 R1 P1 p1 a1 q1) ~~ (acc_el_prop A2 R2 P2 p2 a2 q2).
Proof.
    econstructor.
Qed.