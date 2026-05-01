Set Primitive Projections.

Record Lens (a b c d : Type) : Type :=
{ view : a -> c
; over : (c -> d) -> a -> b
}.

Record LenticularRelation (a b c d : Type) : Type :=
  {
    r_view : a -> c -> Prop;
    r_over : (c -> d -> Prop) -> a -> b -> Prop
  }.

Arguments over {_ _ _ _} _ _ _.
Arguments view {_ _ _ _} _ _.

Definition lens_compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
 ; over := fun f0 : e -> f => over l1 (over l2 f0) |}.

Section ops.
  Context {a b c d : Type} (l : Lens a b c d).

  Definition set (new : d) : a -> b :=
    l.(over) (fun _ => new).
End ops.

Module LensNotations.
  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.
  Bind Scope lens_scope with Lens.

  Notation "X -l> Y" := (Lens X X Y Y)
    (at level 99, Y at level 200, right associativity) : type_scope.
  Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
  Notation "a %= f" := (Lens.over a f) (at level 49, left associativity) : lens_scope.
  Notation "a .= b" := (Lens.set a b) (at level 49, left associativity) : lens_scope.
  Notation "a .^ f" := (Lens.view f a) (at level 45, left associativity) : lens_scope.
  (* level 19 to be compatible with Iris .@ *)
  Notation "a .@ b" := (lens_compose a b) (at level 19, left associativity) : lens_scope.
End LensNotations.

Section LensLaws.
  Context {a b c d : Type} (l : Lens a b c d).

  (* Viewing what you just set gives back the new value *)
  Definition law_view_set : Prop :=
    forall (new : d) (x : a),
      view l (set l new x) = new.

  (* Setting what you just viewed changes nothing *)
  Definition law_set_view : Prop :=
    forall (x : a),
      set l (view l x) x = x.

  (* Two sets at the same focus, last wins *)
  Definition law_set_set : Prop :=
    forall (u v : d) (x : a),
      set l v (set l u x) = set l v x.

  (* over is determined by view and set *)
  Definition law_over_spec : Prop :=
    forall (f : c -> d) (x : a),
      over l f x = set l (f (view l x)) x.

  Record LensLaws : Prop :=
    { lens_view_set : law_view_set
    ; lens_set_view : law_set_view
    ; lens_set_set  : law_set_set
    ; lens_over_spec : law_over_spec
    }.
End LensLaws.

Section LenticularRelationLaws.
  Context {a b c d : Type} (lr : LenticularRelation a b c d).

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
