(** Natural duals via naturality and coherence, by Cyril Cohen and 
   Assia Mahboubi. *)

Require Import ssreflect ssrfun ssrnat.
Require Import Paths Contractible Equivalences HLevel Fibrations.
Import PathNotations.

Open Scope path_scope.
Open Scope equiv_scope.

(* We start with some material missing in the underlying libraries *)

Definition happly {X} {P : X -> Type} {f g : forall x, P x} (p : f = g) (x : X) 
  : f x = g x := match p with identity_refl => 1 end.

Lemma congr_exist {A : Type} {Q : A -> Type}
      {x y : A} {u : Q x} {v : Q y} (p : x = y) :
  transport _ p u = v -> (x; u) = (y; v).
Proof. by case: y / p v => v /= ->. Qed.

Section SigTheory.
Context {X : Type} {T : X -> Type} {Q : forall x, T x -> Type}.

Definition sigA : {x | {Tx | Q x Tx}} -> {u | Q (pr1 u) (pr2 u)} :=
  fun a => let: (x; (Tx; Qx)) := a in 
           ((x; Tx); Qx : (fun u => Q (pr1 u) (pr2 u)) (_ ; _)).

Definition sigA_inverse : {u | Q (pr1 u) (pr2 u)} -> {x | {Tx | Q x Tx}} :=
  fun a => let: ((x; Tx); Qx) := a in (x; (Tx; Qx)).

Lemma sigAK : cancel sigA sigA_inverse. Proof. by move=> [x [Tx Qx]]. Qed.

Lemma sigA_inverseK : cancel sigA_inverse sigA.
Proof. by move=> [[x Tx] Qx]. Qed.

Canonical sigA_equiv := can2_equiv sigAK sigA_inverseK.

End SigTheory.

(* A lemma stolen from the Agda library written by Dan Licata *)
Lemma transport_dep (G V : Type) (B :  forall (y : G), V -> Type) (t1 t2 : G)
  (d : t1 = t2) (Qt1 : forall a : V, B t1 a) :
  transport (fun y => forall x : V, B y x) d Qt1 = 
  (fun x => transport (fun y => B y x) d (Qt1 x)).
Proof. by case: _ /  d Qt1. Qed.

(* An other intersting one I did not find in the agda lib *)
Lemma transport_eq C D (L R : C -> D) (t1 t2 : C) (qq : t1 = t2) 
  (Qt1 : L t1 = R t1) : 
  transport (fun y : C => L y = R y) qq  Qt1 = 
  ((resp L qq)^-1 * Qt1 * resp R qq)%path.
Proof. by case: _ / qq => /=; rewrite mul1p. Qed.


(* We work here under a strong assumption of function extensionality. *)

Axiom funext_axiom : 
  forall X (P : X -> Type) (f g : forall x, P x), is_equiv (@happly X P f g).

Canonical happly_equiv {X} {P : X -> Type} (f g : forall x, P x)
  : (f = g) <~> forall x, f x = g x := is_equiv_equiv (funext_axiom X P f g).

Notation funext := happly^-1.

(* The resp (pmap) operation has some interesting properties under the *)
(* funext assumption. They should hold with weaker versions. *)
Section RespFunExt.
Variables (C : Type) (cc : C).
Lemma resp_app D (x y : C -> D) (qq : forall c : C, x c  = y c) : 
  resp (fun t : C -> D => t cc) (funext qq) = qq cc.
Proof. 
rewrite -[qq in RHS](equivK [equiv of funext]) /=.
by case: _ / (funext qq) => /=.
Qed.

Lemma resp_app_dep D (x y : forall c : C, D c) (qq : forall c : C, x c  = y c) : 
  resp (fun t : forall c : C, D c => t cc) (funext qq) = qq cc.
  rewrite -[qq in RHS](equivK [equiv of funext]) /=.
Proof.  by case: _ / (funext qq) => /=. Qed.

End RespFunExt.


Section InAGroupoidUniverse.


(** We are going to apply the theorems proved below to a universe [U].
   But it turns out all
   theorems are valid more generally with respect to any family, and this is
   much easier to formalize in Coq. So we hypothesize a type family 
   [tp : U -> Type]. *)

(* Think of [U] as a small universe (but can be anything). *)
Definition U := Type.

(* We suppose than any inhab of U is a groupoid. We here only use the 
   truncation:*)
Hypothesis my_groupoids : forall (X : U) (x y : X) (p1 p2 : x = y) 
  (h1 h2 : p1 = p2), h1 = h2.


(* Think of [tp] as a coercion from the universe to types. *)
Parameter tp : U -> Type. 

(* We can actually declare [tp] to be a coercion, so Coq will insert it 
   automagically. *)
Coercion tp : U >-> Sortclass.

(* Fix a type [A] in [U]. *)
Parameter A : U.

(** The following is called the dual of [A]. *)
Definition A' := (forall X : U, (A -> X) -> X).

(* We know that in nice enough models of polymorphism [A] and [A'] are 
   isomorphic. We explore the situation in type theory. *)

(** First observe that there are maps between [A] and [dual A]. *)

Definition eta : A -> A' := fun (a : A) (X : U) (f : A -> X) => f a.

Definition rho : A' -> A := fun (h : A') => h A (fun a : A => a).

(** [eta] is a section of [rho], definitionally. This is very convenient. 
   NB: We should never have to use retr. *)
Lemma retr (a : A) : rho (eta a) = a.
Proof.
  reflexivity.
Defined.

(** We impose an additional condition on elements of [A'], which is
   just a form of naturality. *)
Definition natural (h : A') : Type :=
  forall (X Y : U) (f : X -> Y) (g : A -> X), h Y (f \o g) = f (h X g).

(** And then we ned an additional condition on naturality. *)
Definition coherent {h : A'} (p : natural h) :=
  forall (X Y Z : U) (e : X -> Y) (f : Y -> Z) (g : A -> X),
    p Y Z f (e \o g) * resp f (p X Y e g) = p X Z (f \o e) g.

Definition eta_natural (a : A) : natural (eta a) := fun _ _ _ _ => 1.

Definition eta_coherent (a : A) : coherent (eta_natural a) :=
  fun _ _ _ _ _ _ => 1.

(* Interesting roperties of the coherent predicate *)
Section CoherenceTheory.
Variables (h : A') (p : natural h) (c : coherent p).

Lemma cohrent_p1 X f : p X X id f = 1.
Proof. by have /(canRL (mulKp _)) := c _ _ _ id id f; rewrite mulVp respidp. Qed.

Lemma coherent_fg X Y f g : 
  p X Y f g = p A Y (f \o g) id * (f`_* (p A X g id)^-1)%path.
Proof.
have := c _ _ _ g f id.
move/(congr1 (fun x => x * (f`_* (p A X g id))^-1)%path).
by rewrite mulpK resppV.
Qed.


(* We use the groupoid hypothesis to show that the type of coherence proofs *)
(* of a natual inhabitant of A' is contractile *)

Lemma coherent_is_contr : is_contr (coherent p).
Proof.
by exists c => coh2; do 6! (apply: funext => ?); apply: my_groupoids.
Qed.

End CoherenceTheory.


(* Now the definition of the actual dual isomorphic to A *)

Let P (h : A') := { p : natural h & coherent p }.

(* Inductive unit' : U := tt' : unit'. *)

Definition A'' := { h : A' &  P h}.

Definition u (a : A) : A'' := (eta a ; (eta_natural a ; eta_coherent a)).

Definition v (hpt : A'') : A := rho (pr1 hpt).
  
Lemma uK : cancel u v. Proof. done. Qed.

Definition alpha (h : A') (p : natural h) : eta (rho h) = h :=
  funext (fun X => funext (fun f => (p A X f id)^-1%path)).


Lemma vK : cancel v u.
Proof.
move=> [h [p c]]; rewrite /u /=; apply: (resp sigA)^-1 => /=.
suff q : (eta (h A id); eta_natural (h A id)) = (h; p).
  apply: (congr_exist q); apply: is_contr_eq.
  exact: coherent_is_contr.
apply: (congr_exist (alpha _ p)) => /=.
apply: funext => X; apply: funext => Y; apply: funext => f; apply: funext => g.
rewrite 4! transport_dep /eta_natural /= [p X Y f g]coherent_fg // transport_eq. 
congr (_ * _) => /=.
  set q := (M in _ `_* M).
  set F := (M in M `_* _).
  have -> : F `_* q = ((fun z => z (f \o g)) \o (fun y => y Y))`_* q.
    by rewrite resppcomp.
  by rewrite resppcomp 2!resp_app_dep invpK.
set q := (M in _ `_* M).
set F := (M in M `_* _).
have -> : F `_* q = ((fun z => f z) \o (fun w => w g) \o (fun y => y X)) `_* q.
  by rewrite !resppcomp.
by rewrite 3!resppcomp 2!resp_app_dep /= respidp.
Qed.

Definition A_equiv_A'': A <~> A'' := can2_equiv uK vK.

End InAGroupoidUniverse.