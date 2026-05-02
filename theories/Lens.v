Set Primitive Projections.

Record Polymorphic (a b c d : Type) : Type := {
  view : a -> c;
  set : d -> a -> b
}.

Definition Simple (a c : Type) : Type := Polymorphic a a c c.

Record Relational (a b c d : Type) : Type := {
  r_view : a -> c -> Prop;
  r_over : d -> a -> b -> Prop
}.

Arguments view {_ _ _ _} _ _.
Arguments set {_ _ _ _} _ _ _.

Definition compose {a b c d e f : Type}
           (l0 : Polymorphic a b c d) (l1 : Polymorphic c d e f)
: Polymorphic a b e f :=
{| view := fun x : a => view l1 (view l0 x)
 ; set := fun (u : f) (x : a) => set l0 (set l1 u (view l0 x)) x |}.

Definition product {a c c' : Type}
           (l0 : Simple a c) (l1 : Simple a c')
           : Simple a (c * c') :=
{| view := fun x : a => (view l0 x, view l1 x)
 ; set := fun (p : c * c') (x : a) =>
   let '(u, v) := p in
   set l0 u (set l1 v x) |}.

Definition over {a b c d : Type} (l : Polymorphic a b c d) (f : c -> d) : a -> b :=
  fun x => set l (f (view l x)) x.

(* Viewing what you just set gives back the new value *)
Definition view_set' {a c : Type} (l : Simple a c) : Prop :=
  forall (new : c) (x : a),
    view l (set l new x) = new.

(* Setting what you just viewed changes nothing *)
Definition set_view' {a c : Type} (l : Simple a c) : Prop :=
  forall (x : a),
    set l (view l x) x = x.

(* The view completely determines the source, present in bijective lenses *)
Definition strong_set_view' {a c : Type} (l : Simple a c) : Prop :=
  forall (x x' : a),
    set l (view l x) x' = x.

(* Two sets at the same focus, last wins *)
Definition set_set' {a c : Type} (l : Simple a c) : Prop :=
  forall (u v : c) (x : a),
    set l v (set l u x) = set l v x.

(* over is determined by view and set *)
Definition over_spec' {a c : Type} (l : Simple a c) : Prop :=
  forall (f : c -> c) (x : a),
    over l f x = set l (f (view l x)) x.

Record Lawful {a c : Type} (l : Simple a c) : Prop :=
  { view_set : @view_set' a c l
  ; set_view : @set_view' a c l
  ; set_set  : @set_set' a c l
  }.

Arguments view_set {a c l}.
Arguments set_view {a c l}.
Arguments set_set {a c l}.

Definition commutative {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c') : Prop :=
  forall (x : a) (v : c) (u : c'),
    set l0 v (set l1 u x) = set l1 u (set l0 v x).

Definition independent_view_over {a c : Type} (l0 l1 : Simple a c) : Prop :=
  forall (x : a) (u : c),
    view l0 (set l1 u x) = view l0 x.

Theorem lawful_product {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c')
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (compatible : commutative l0 l1) :
  Lawful (product l0 l1).
Proof.
  apply Build_Lawful.
  - unfold view_set'. intros [u v] x. simpl. f_equal.
    + apply (view_set lawful0).
    + rewrite compatible. apply (view_set lawful1).
  - unfold set_view'. intros x. simpl. rewrite (set_view lawful1).
    apply (set_view lawful0). 
  - unfold set_set'. intros [u u'] [v v'] x. simpl.
    rewrite <- compatible. rewrite (set_set lawful1). rewrite (set_set lawful0).
    reflexivity.
Qed.

End LensLaws.

Section LenticularRelationLaws.
  Context {a c : Type} (lr : LenticularRelation a a c c).

  (* Viewing is deterministic: if you can view x as both u and v, they're equal *)
  Definition law_r_view_det : Prop :=
    forall (x : a) (u v : c),
      r_view lr x u -> r_view lr x v -> u = v.

  (* Every element has something to view *)
  Definition law_r_view_total : Prop :=
    forall (x : a), exists (u : c), r_view lr x u.

  (* PutGet: if you update with a relation that maps c to d,
     the viewed result of the new state is related to the old focus *)
  Definition law_r_view_over : Prop :=
    forall (f : c -> d -> Prop) (x : a) (y : b) (u : c) (v : d),
      r_view lr x u ->
      f u v ->
      r_over lr f x y ->
      r_view lr y v.

  (* GetPut: updating with the identity relation changes nothing *)
  Definition law_r_over_id : Prop :=
    forall (x : a) (y : b),
      r_over lr (fun u v => u = v) x y ->
      x = y.

  (* PutPut: two updates composed equals the second update *)
  Definition law_r_over_over : Prop :=
    forall (f g : c -> d -> Prop) (x : a) (y z : b),
      r_over lr f x y ->
      r_over lr g y z ->
      r_over lr (fun u w => exists v, f u v /\ g v w) x z.

  (* Locality: over only affects the focus *)
  Definition law_r_over_local : Prop :=
    forall (f : c -> d -> Prop) (x : a) (y : b) (u : c),
      r_view lr x u ->
      r_over lr f x y ->
      exists v, f u v /\ r_view lr y v.

  Record LenticularRelationLaws : Prop :=
    { lr_view_det   : law_r_view_det
    ; lr_view_total : law_r_view_total
    ; lr_view_over  : law_r_view_over
    ; lr_over_id    : law_r_over_id
    ; lr_over_over  : law_r_over_over
    ; lr_over_local : law_r_over_local
    }.
End LenticularRelationLaws.

Section LensToLenticular.
  (* Every lawful lens gives rise to a lawful lenticular relation *)
  Context {a b c d : Type} (l : Lens a b c d) (ll : LensLaws l).

  Definition lens_to_lenticular : LenticularRelation a b c d :=
    {| r_view := fun x u => view l x = u
     ; r_over := fun f x y => exists u v, view l x = u /\ f u v /\ set l v x = y
    |}.

  Lemma lens_to_lenticular_laws : LenticularRelationLaws lens_to_lenticular.
  Proof.
    constructor; unfold lens_to_lenticular; simpl.
    - (* view_det *) intros x u v <- <-. reflexivity.
    - (* view_total *) intros x. exists (view l x). reflexivity.
    - (* view_over *)
      intros f x y u v Hu Hf (u' & v' & Hu' & Hf' & <-).
      rewrite <- Hu in Hu'. rewrite <- Hu'.
      rewrite ll.(lens_view_set). congruence.
    - (* over_id *)
      intros x y (u & v & Hu & <- & Hy).
      rewrite <- ll.(lens_set_view). rewrite <- Hu. exact Hy.
    - (* over_over *)
      intros f g x y z (u & v & Hu & Hf & <-) (u' & w & Hu' & Hg & <-).
      exists u, w.
      rewrite ll.(lens_view_set) in Hu'.
      split. exact Hu.
      split. exists v. exact (conj Hf (Hu' ▸ Hg)).
      rewrite ll.(lens_set_set). congruence.
    - (* over_local *)
      intros f x y u Hu (u' & v & Hu' & Hf & <-).
      exists v.
      rewrite <- Hu in Hu'.
      split. congruence.
      rewrite ll.(lens_view_set). reflexivity.
  Qed.
End LensToLenticular.
Module LensNotations.
  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.
  Bind Scope lens_scope with Lens.

  Notation "X -l> Y" := (Simple X Y)
    (at level 99, Y at level 200, right associativity) : type_scope.
  Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
  Notation "a %= f" := (Lens.over a f) (at level 49, left associativity) : lens_scope.
  Notation "a .= b" := (Lens.set a b) (at level 49, left associativity) : lens_scope.
  Notation "a .^ f" := (Lens.view f a) (at level 45, left associativity) : lens_scope.
  (* level 19 to be compatible with Iris .@ *)
  Notation "a .@ b" := (lens_compose a b) (at level 19, left associativity) : lens_scope.
End LensNotations.
