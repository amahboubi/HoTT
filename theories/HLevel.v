Require Import ssreflect ssrfun ssrbool ssrnat.
Require Import Paths Fibrations Contractible Equivalences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.
Open Scope equiv_scope.

Fixpoint has_hlevel (n : nat) : Type -> Type :=
  if n is m.+1 then (fun A => forall x y : A, has_hlevel m (x = y))
  else is_contr.

Arguments pmap {A B x y} f _.

Lemma pmapJ A B C (f g : A -> B) (p : f =1 g) (h : B -> C)
      (x y : A) (q : f x = f y) :
  h`_* (q ^ p) = (h`_* q) ^ (fun x => h`_* (p x)).
Proof. by rewrite !pmapM -pmapV. Qed.

Lemma eq1_conjp {A B} {x y : A} (f g : A -> B)
  (p1 p2 : f =1 g) (q : f x = f y) : 
  (forall t, p1 t = p2 t) -> q ^ p1 = q ^ p2.
Proof. by move=> coh; rewrite conjpE !coh. Qed.

Lemma equiv_pmapRJ A B (e : A <~> B) x y (u : e x = e y) :
     e`_* ((e^-1)%equiv`_* u ^ (equivK e)) = u.
Proof.
by rewrite (pmapJ (equivK _)) (eq1_conjp _ (pmap_equivK _)); apply: can_pmap.
Qed.

Section PmapEquiv.
Variables (A B : Type) (x y : A) (e : A <~> B).
Arguments pmap {A B x y f} _.

Definition pmap_inverse : (e x = e y) -> x = y :=
  fun p => (e^-1`_* p)%equiv ^ (equivK e).

Lemma pmapK : cancel pmap pmap_inverse. Proof. exact: can_pmap. Qed.
Lemma pmap_inverseK : cancel pmap_inverse pmap.
Proof. exact: equiv_pmapRJ. Qed.

Canonical equiv_pmap : x = y <~> e x = e y := can2_equiv pmapK pmap_inverseK.

End PmapEquiv.

Lemma equiv_has_hlevel n U V : U <~> V -> has_hlevel n U -> has_hlevel n V.
Proof.
elim: n U V => /= [U V e U_is_contr | n ihn U V e U_level_n x y].
  exact: equiv_contr_is_contr e.
exact: (ihn _ _ [equiv of (pmap e^-1)^-1]).
Qed.

Lemma retract_has_hlevel n U V (f : U -> V) (g : V -> U) (gK : cancel g f) :
      has_hlevel n U -> has_hlevel n V.
Proof.
elim: n U V f g gK => /= [| n ihn] U V f g gK.
  move=> U_is_contr; exists (f (contr_elt U_is_contr)) => a.
  by rewrite -[a]gK; congr f; apply: is_contr_eq.
(*   exact: equiv_contr_is_contr e. *)
(* exact: (ihn _ _ [equiv of (pmap e^-1)^-1]). *)
admit.
Qed.
