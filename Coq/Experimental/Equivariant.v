(**** WORK IN PROGRESS WITH Egbert Rijke ***)

(* How far can we pretend that equivalences are paths? *)

Add LoadPath "..".

Require Import Paths Fibrations Contractible Funext HLevel
  Equivalences FiberEquivalences FunextEquivalences Univalence.
Require Import ExtensionalityAxiom.

(** Suppose [P : Type -> Type] and [A <~> B]. Is it the case that [P A <~> P B], or more
   precisely, can we always convert [e : A <~> B] to [map P e : P A <~> P B]? Let us call
   a [P] *equivariant* when it has this property. We also require that the passage
   [eq_map] from [A <~> B] to [P A <~> P B] behaves compositionally.*)

Structure Equivariant := {
  eq_ty :> Type -> Type ;
  eq_map : forall (A B : Type), A <~> B -> eq_ty A <~> eq_ty B ;
  eq_id : forall (A : Type) (x : eq_ty A), eq_map A A (idequiv A) x ~~> x ;
  eq_comp : forall (A B C : Type) (e : A <~> B) (f : B <~> C) (x : eq_ty A),
              eq_map B C f (eq_map A B e x) ~~> eq_map A C (equiv_compose e f) x
}.

Implicit Arguments eq_map [A B].
Implicit Arguments eq_id [A].
Implicit Arguments eq_comp [A B C].

(** We also need a more general notion of equivariance of families over equivariant families. *)

Structure EquivariantFamily (P : Equivariant) := {
  fam :> forall (A : Type), P A -> Type ; 
  fam_map : forall (A B : Type) (e : A <~> B) (x : P A), fam A x <~> fam B (eq_map P e x) ;
  fam_id : forall (A : Type) (x : P A) (y : fam A x), eq_id P x # fam_map A A (idequiv A) x y ~~> y ;
  fam_comp : forall (A B C : Type) (e : A <~> B) (f : B <~> C) (x : P A) (y : fam A x),
          eq_comp P e f x # fam_map B C f (eq_map P e x) (fam_map A B e x y) ~~>
          fam_map A C (equiv_compose e f) x y
}.

Implicit Arguments fam [P].
Implicit Arguments fam_map [P A B].

(** We expect all definable families to be equivariant. So we start showing that equivariance
   is closed under various operations.*)

Section CartesianProduct.
  (* An exercise: cartesian products *)

  Definition prod_map (P Q : Equivariant) (A B : Type) (e : A <~> B) :
    (P A * Q A <~> P B * Q B)%type.
  Proof.
    apply product_equiv.
    exact (eq_map P e).
    exact (eq_map Q e).
  Defined.

  Theorem prod_equivariant (P Q : Equivariant) : Equivariant.
  Proof.
    refine
      {| eq_ty := fun A => (P A * Q A)%type ;
         eq_map := prod_map P Q
      |}.
    intros A [x y]; apply prod_path_equiv; simpl; split; apply eq_id.
    intros A B C e f [x y].
    apply prod_path_equiv; simpl; split; apply eq_comp.
  Defined.
End CartesianProduct.

Section DisjointSum.
  (** Another exercise: disjoint sums *)

  (** We would expect this lemma in [UsefulEquivalences]. *)
  Lemma sum_equiv (A A' B B' : Type) :
    (A <~> A') -> (B <~> B') -> (A + B <~> A' + B').
  Proof.
    intros e f.
    apply (equiv_from_hequiv
      (fun (u : A + B) => match u with inl x => inl _ (e x) | inr y => inr _ (f y) end)
      (fun (v : A' + B') => match v with inl x' => inl _ (e^-1 x') | inr y' => inr _ (f^-1 y') end)).
    intros [x'|y']; apply map, inverse_is_section.
    intros [x|y]; apply map, inverse_is_retraction.
  Defined.

  Definition sum_map (P Q : Equivariant) (A B : Type) (e : A <~> B) :
    (P A + Q A <~> P B + Q B)%type.
  Proof.
    apply sum_equiv; apply eq_map; exact e.
  Defined.
    
  Theorem sum_equivariant (P Q : Equivariant) : Equivariant.
  Proof.
    refine
      {| eq_ty := fun A => (P A + Q A)%type ;
         eq_map := sum_map P Q
       |}.
    intros A [u|v]; unfold sum_map, sum_equiv; simpl; apply map, eq_id.
    intros A B C e f [u|v]; unfold sum_map, sum_equiv; simpl; apply map, eq_comp.
  Defined.
End DisjointSum.

Section DependentSum.
  (** Now something slightly more involved: total spaces. *)

  (** This one should go to [FiberEquivalences]. *)
  Lemma total_equiv (A B : Type) (P : fibration A) (Q : fibration B) (e : A <~> B)
    (f : (forall x : A, P x <~> Q (e x))) :
    total P <~> total Q.
  Proof.
    apply fibseq_total_equiv with (e := e) (g := (fun x => f x)).
    intro x; apply (equiv_is_equiv (f x)).
  Defined.

  Definition total_map (P : Equivariant) (Q : EquivariantFamily P)
    (A B : Type) (e : A <~> B) : total (Q A) <~> total (Q B).
  Proof.
    apply total_equiv with (e := eq_map P e) (P := Q A) (Q := Q B).
    intro x.
    apply fam_map.
  Defined.
  
  (** The dependent sum of an equivariant family is equivariant. *)

  Theorem total_equivariant (P : Equivariant) (Q : EquivariantFamily P) : Equivariant.
  Proof.
    refine
      {| eq_ty := (fun A => total (Q A)) ;
         eq_map := total_map P Q
      |}.
    intros A [x y]; apply total_paths_equiv; simpl.
    exists (eq_id P x).
    now apply fam_id.
    intros A B C e f [x y]; apply total_paths_equiv; simpl.
    exists (eq_comp P e f x); simpl.
    now apply fam_comp.
  Defined.

End DependentSum.

Section DependentProduct.

  (** The final test of course are the products. After attacking the problem with brute force
     and ignorance, one gets the feeling that equivariance is closed under products, but that
     the proof of such a fact is not easy, mostly because of intricate rewriting that Coq seems
     unable to do. So we first prepare several lemmas that will help us get over Coq's inability
     to do fancy rewriting (or my inability to use it).

     Let us describe the general problem. On several occasions we have something like [p x
     # f x] and a path [q : x ~~> y]. We would like to rewrite [f x] to [f y] with respect
     to [q]. But if we do this naively, Coq thinks we want to change all occurrences of [x]
     to [y], so it tells us that [p y # f y] is not well-typed. Normally, in such situations
     one could use [rewrite q at ...] but that requires the [Setoid] library, which makes us
     unhappy. So we have to do some manual work.
*)

  Lemma equiv_map_path (A B : Type) (e f : A <~> B) :
    equiv_map e ~~> equiv_map f -> e ~~> f.
  Proof.
    intro p.
    destruct e as [e E].
    destruct f as [f F].
    simpl in p.
    induction p.
    rewrite (prop_path (is_equiv_is_prop e) E F).
    apply idpath.
  Defined.
  
  Lemma equiv_extensionality (A B : Type) (e f : A <~> B) :
    e === f -> e ~~> f.
  Proof.
    intro H.
    apply equiv_map_path.
    now by_extensionality.
  Defined.

  Lemma equiv_inverse_left (A B : Type) (e : A <~> B) :
    equiv_compose (equiv_inverse e) e ~~> idequiv B.
  Proof.
    apply equiv_extensionality.
    intro y.
    unfold equiv_compose, equiv_inverse; simpl.
    path_via (e (e^-1 y)).
    rewrite inverse_is_section.
    apply idpath.
  Defined.

  Lemma eq_map_inverse (P : Equivariant) (A B : Type) (e : A <~> B) :
    eq_map P (equiv_inverse e) ~~> equiv_inverse (eq_map P e).
  Proof.
    apply equiv_extensionality.
    intro y.
    simpl.
    equiv_moveleft.
    rewrite eq_comp.
    rewrite equiv_inverse_left.
    apply eq_id.
  Defined.

  (* Again something that should find its place elsewhere. *)

  Definition inverse_triangle' {A B : Type} (e : A <~> B) y :
    (map (equiv_inverse e) (inverse_is_section e y)) ~~> inverse_is_retraction e ((equiv_inverse e) y).
  Proof.
    admit.
  Defined.

  Lemma section_equiv (A B : Type) (P : fibration A) (Q : fibration B)
    (e : A <~> B) (f : forall x : A, P x <~> Q (e x)) :
    section P <~> section Q.
  Proof.
    pose (j := fun (h : section P) (y : B) => inverse_is_section e y # f (e^-1 y) (h (e^-1 y))).
    pose (k := fun (g : section Q) (x : A) => (f _)^-1 (g (e x))).
    apply (equiv_from_hequiv j k).
    intros s.
    unfold j, k.
    apply funext_dep; intro y.
    rewrite (inverse_is_section (f (e^-1 y))).
    rewrite (inverse_is_section e).
    now auto.
    intros s; unfold j, k.
    apply funext_dep; intro x.
    rewrite <- inverse_triangle.
    rewrite (inverse_is_retraction e x).
    now hott_simpl.
  Defined.
  
  Definition section_map (P : Equivariant) (Q : EquivariantFamily P)
    (A B : Type) (e : A <~> B) : section (Q A) <~> section (Q B).
  Proof.
    apply section_equiv with (P := Q A) (Q := Q B) (e := eq_map P e).
    apply (fam_map Q e).
  Defined.

  Lemma eq_map_inverse' (P : Equivariant) (A B : Type) (e : A <~> B) (y : P B) :
    (eq_map P e)^-1 y ~~> eq_map P (equiv_inverse e) y.
  Proof.
    rewrite eq_map_inverse.
    apply idpath.
  Defined.

  Lemma eq_map_idequiv_inverse (P : Equivariant) (Q : EquivariantFamily P)
    (A : Type) (x : P A) :
    eq_map P (idequiv A) ^-1 x ~~> x.
  Proof.
    equiv_moveright.
    apply opposite, eq_id.
  Defined.

  Definition section_map_path (P : Equivariant) (Q : EquivariantFamily P)
    (A : Type) (s : section (Q A)) (x : P A) :
    section_map P Q A A (idequiv A) s x ~~> s x.
  Proof.
    unfold section_map, section_equiv; simpl.
    set (e := eq_map P (idequiv A)).
    set (p := inverse_is_section e).
    set (g := fam_map Q (idequiv A)).
  Admitted.

  (* Useless above this line. *)

  Lemma equiv_compose_assoc (A B C D : Type) (f : A <~> B) (g : B <~> C) (h : C <~> D) :
    equiv_compose f (equiv_compose g h) ~~> equiv_compose (equiv_compose f g) h.
  Proof.
    apply equiv_extensionality.
    intro; apply idpath.
  Defined.

  Lemma equiv_compose_inverse (A B C : Type) (e : A <~> B) (f : B <~> C) :
    equiv_compose (equiv_inverse f) (equiv_inverse e) ~~> equiv_inverse (equiv_compose e f).
  Proof.
    apply equiv_extensionality.
    intro; apply idpath.
  Defined.

  Lemma equiv_left_inverse (A B : Type) (e : A <~> B) :
    equiv_compose (equiv_inverse e) e ~~> idequiv B.
  Proof.
    apply equiv_extensionality.
    intro; unfold idequiv, idmap; simpl.
    apply inverse_is_section.
  Defined.

  Lemma eq_comp_path (P : Equivariant) {A B C : Type} (e : A <~> B) (f : B <~> C) :
    eq_map P (equiv_compose e f) ~~> equiv_compose (eq_map P e) (eq_map P f).
  Proof.
    apply equiv_extensionality.
    intro x.
    apply opposite.
    unfold equiv_compose, compose; simpl; apply eq_comp.
  Defined.

  Lemma eq_map_comp_inverse (P : Equivariant) {A B C : Type} (e : A <~> B) (f : B <~> C):
    eq_map P (equiv_compose e f) ^-1 ~~> eq_map P (equiv_compose (equiv_inverse f) (equiv_inverse e)).
  Proof.
    apply funext_dep; intro z.
    equiv_moveright.
    rewrite eq_comp.
    rewrite equiv_compose_inverse.
    rewrite equiv_left_inverse.
    apply opposite, eq_id.
  Defined.

  Lemma inverse_is_section_comp {A B C : Type} (e : A <~> B) (f : B <~> C) (z : C) :
    inverse_is_section (equiv_compose e f) z ~~>
    map f (inverse_is_section e (f^-1 z)) @ inverse_is_section f z.
  Proof.
    unfold inverse_is_section, equiv_compose; simpl.
    apply idpath.
  Defined.

  Lemma inverse_is_stupid (P : Equivariant) {A B C : Type} (e : A <~> B) (f : B <~> C) (z : P C) :
    (inverse_is_section (eq_map P (equiv_compose e f)) z) ~~>
    transport
      (P := fun (h : P A <~> P C) => h (h^-1 z) ~~> z)
      (! (eq_comp_path P e f))
      (map (eq_map P f) (inverse_is_section (eq_map P e) ((eq_map P f)^-1 z)) @ inverse_is_section (eq_map P f) z).
  Proof.
    rewrite (eq_comp_path P e f).
    hott_simpl.
  Defined.
 
  Lemma transport_moveright (A : Type) (P : fibration A) (x y : A) (p : x ~~> y) (u : P x) (v : P y) :
    (u ~~> !p # v) -> (p # u ~~> v).
  Proof.
    intro q.
    induction p.
    hott_simpl.
  Defined.

  (* Lemma trans_rewrite {A B : Type} (P : fibration B) (f : A -> B) (u : section (P o f)) {x y : A} (q : y ~~> x) : *)
  (*   u x ~~> map f q # u y. *)
  (* Proof. *)
  (*   path_induction. *)
  (* Defined. *)

  Lemma trans_rewrite {A B : Type} (P : fibration B) (f : A -> B) (u : section (P o f)) {x y : A} (q : y ~~> x) :
    u x ~~> map f q # u y.
  Proof.
    path_induction.
  Defined.


  Ltac trans_rewrite_in ux q :=
    match type of q with ?y ~~> ?x =>
      let v := fresh in
        pose (v := ux) ;
          pattern x in v ;
          match goal with v := ?u x |- _  =>
            clear v ;
            let A := type of x in
            let p := fresh "p" in
              rewrite (trans_rewrite _ (fun (x : A) => A) u q : u x ~~> map q # u y)
          end
    end.

  Ltac trans_detect_left q :=
    match goal with |- ?ux ~~> _ =>
      match type of q with ?y ~~> ?x =>
        let v := fresh in
          pose (v := ux) ;
            pattern x in v ;
              match goal with v := ?u x |- _ =>
                clear v ;
                let t := fresh "ty" in
                  let tu := type of u in
                    let A_ty := fresh in
                      let x_ty := type of x in
                  pose (t := tu) ; pose (A_ty := x_ty)
              end
      end
    end.

  Ltac trans_detect_right q :=
    match goal with |- _ ~~> ?ux =>
      match type of q with ?y ~~> ?x =>
        let v := fresh in
          pose (v := ux) ;
            pattern x in v ;
              match goal with v := ?u x |- _ =>
                idtac x ; idtac u ;
                clear v ;
                let t := fresh "ty" in
                  let tu := type of u in
                    let A_ty := fresh "A_ty" in
                      let x_ty := type of x in
                  pose (t := tu) ; pose (A_ty := x_ty)
              end
      end
    end.
      
  (* Ltac trans_rewrite f q := *)
  (*   match type of q with ?y ~~> ?x => *)
  (*     match goal with *)
  (*       | context ctx [?u x *)
  (*     end *)
  (*   end. *)

  Lemma inverse_is_section_rewrite {A B : Type} (e f : A <~> B) (p : e ~~> f) (y : B) :
    inverse_is_section e y ~~>
    map (fun (e : A <~> B) => e (e^-1 y)) p @ inverse_is_section f y.
  Proof.
    path_induction.
  Defined.

  Lemma is_section_equiv_on_Q {P : Equivariant} (Q : EquivariantFamily P) {A B : Type}
    (e : A <~> B) (y : P B) :
    Q B (eq_map P e (eq_map P e ^-1 y)) <~> Q B y.
  Proof.
    apply path_to_equiv, map.
    apply inverse_is_section.
  Defined.

  (* Lemma fam_map_is_section_equiv {P : Equivariant} (Q : EquivariantFamily P) {A B : Type} *)
  (*   (e : A <~> B) (y : P B) u : *)
  (*   (fam_map Q (equiv_inverse e) y)^-1 u ~~> *)
  (*   (is_section_equiv_on_Q Q e y) (fam_map Q e (eq_map P e ^-1 y) u). *)
    

  Definition section_equivariant (P : Equivariant) (Q : EquivariantFamily P) : Equivariant.
  Proof.
    refine
      {| eq_ty := (fun A => section (Q A)) ;
         eq_map := section_map P Q
      |}.
    (* Identity *)
    intros A s.
    apply funext_dep; intro x.
    unfold section_map, section_equiv; simpl.
    generalize (inverse_is_section (eq_map P (idequiv A)) x).
    generalize ((eq_map P (idequiv A) ^-1) x).
    intros x' p.
    pose (q := (!(eq_id P x') @ p)).
    assert (h : p ~~> eq_id P x' @ q); unfold q; hott_simpl.
    rewrite h.
    generalize q; intro r; induction r.
    hott_simpl.
    now apply fam_id.
    (* Composition. *)
    intros A B C e f s.
    apply funext_dep; intro z.
    unfold section_map, section_equiv; simpl.
    rewrite inverse_is_section_rewrite with (p := eq_comp_path P e f).
    rewrite inverse_is_section_comp.
    hott_simpl.
    apply map.
    equiv_moveright.

    


    match goal with |- ?lefty ~~> ?righty => pose (left := lefty) ; pose (right := righty) end.

    rewrite (eq_comp_path P e f) in right.

    set (E := eq_map P e).
    set (F := eq_map P f).
    set (r := inverse_is_section (eq_map P (equiv_compose e f)) z
   # (fam_map Q (equiv_compose e f) ((eq_map P (equiv_compose e f) ^-1) z))
       (s ((eq_map P (equiv_compose e f) ^-1) z))).
    pose (la := eq_comp_path P e f).
    set (qq := eq_map P (equiv_compose e f)) in * |- *.

    assert (pp : aa ~~> aa).
    unfold qq in aa.
    rewrite (eq_comp_path
    fold aa in r.
    pattern aa in r.
    unfold r.
    rewrite pp.
    

    rewrite la in aa.
    
    simpl in aa.

    rewrite (idpath _ : xx ~~> xx) in r.
    Show Proof.



    trans_rewrite_in (inverse_is_section (eq_map P (equiv_compose e f)) z) (eq_map_comp_inverse P e f).
  Admitted.
End DependentProduct.


