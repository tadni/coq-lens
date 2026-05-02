Set Primitive Projections.

Record Polymorphic (a b c d : Type) : Type := {
  view : a -> c;
  set : d -> a -> b
}.
Arguments view {_ _ _ _} _ _.
Arguments set {_ _ _ _} _ _ _.

Definition Simple (a c : Type) : Type := Polymorphic a a c c.

Record Relational (a b c d : Type) : Type := {
  r_view : a -> c -> Prop;
  r_set : d -> a -> b -> Prop
}.
Arguments r_view {_ _ _ _} _ _.
Arguments r_set {_ _ _ _} _ _ _.

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

Section Counterexample.
(* A = option bool * bool,  l0 focuses on the first component,
   l1 focuses on the second but twists the first via a 3-cycle *)

(*  sigma v w = identity when v = w
    sigma false true  = (None ↦ Some false ↦ Some true ↦ None)  (3-cycle)
    sigma true  false = its inverse                              *)
Definition sigma (v w : bool) (u : option bool) : option bool :=
  match v, w with
  | false, true  => match u with
                    | None       => Some false
                    | Some false => Some true
                    | Some true  => None
                    end
  | true,  false => match u with
                    | None       => Some true
                    | Some true  => Some false
                    | Some false => None
                    end
  | _,     _     => u
  end.

Definition l0 : Simple (option bool * bool) (option bool) :=
  {| view := fst
   ; set  := fun w x => (w, snd x) |}.

Definition l1 : Simple (option bool * bool) bool :=
  {| view := snd
   ; set  := fun w x => (sigma (snd x) w (fst x), w) |}.

Lemma lawful_l0 : Lawful l0.
Proof.
  constructor.
  - intros new [u v]; reflexivity.
  - intros [u v]; reflexivity.
  - intros u v [a b]; reflexivity.
Qed.

(* set_set relies on the cocycle condition sigma w w' (sigma v w u) = sigma v w' u,
   proved by exhaustive case analysis on the 2*2*2*3 = 24 cases *)
Lemma lawful_l1 : Lawful l1.
Proof.
  constructor.
  - intros new [u v]; reflexivity.
  - intros [u v]; destruct u as [[]|], v; reflexivity.
  - intros u v [a b]; destruct u, v, a as [[]|], b; reflexivity.
Qed.

(* The product view is (a,b)↦(a,b) and setter ignores the old value entirely,
   so it is the full-replacement (bijective) lens on option bool * bool *)
Lemma lawful_product_l0_l1 : Lawful (product l0 l1).
Proof.
  constructor.
  - intros [u v] [a b]; reflexivity.
  - intros [a b]; destruct a as [[]|], b; reflexivity.
  - intros [u u'] [v v'] [a b]; reflexivity.
Qed.

Lemma not_lawful_product_l1_l0 : ~ Lawful (product l1 l0).
Proof.
  intro H.
  specialize (view_set H (true, None) (None, false)).
  simpl; discriminate.
Qed.

(* The product is also bijective: setting the viewed value gives the same result
   regardless of the starting point *)
Lemma strong_set_view_product : strong_set_view' (product l0 l1).
Proof.
  intros [a b] [a' b']; destruct a as [[]|], b; reflexivity.
Qed.

(* Despite all of the above, the two lenses do not commute:
   set l0 (Some false) (set l1 true  (None, false)) = (Some false, true)
   set l1 true  (set l0 (Some false) (None, false)) = (Some true,  true) *)
Lemma not_commutative_l0_l1 : ~ commutative l0 l1.
Proof.
  unfold commutative; intro H.
  specialize (H (None, false) (Some false) true).
  simpl in H; discriminate.
Qed.

End Counterexample.

Section BothLawfulImpliesCommutative.
Context {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c').
Context (hl0 : Lawful l0) (hl1 : Lawful l1).
Context (hp01 : Lawful (product l0 l1)) (hp10 : Lawful (product l1 l0)).

(* set l0 cannot disturb l1's view *)
Lemma ind_01 : forall (u : c) (x : a), view l1 (set l0 u x) = view l1 x.
Proof.
  intros u x.
  pose proof (view_set hp01 (u, view l1 x) x) as H; simpl in H.
  rewrite (set_view hl1 x) in H.
  exact (f_equal snd H).
Qed.

(* set l1 cannot disturb l0's view *)
Lemma ind_10 : forall (v : c') (x : a), view l0 (set l1 v x) = view l0 x.
Proof.
  intros v x.
  pose proof (view_set hp10 (v, view l0 x) x) as H; simpl in H.
  rewrite (set_view hl0 x) in H.
  exact (f_equal snd H).
Qed.

Theorem both_products_lawful_commutative : commutative l0 l1.
Proof.
  unfold commutative; intros x v u.
  (* view l0 (set l1 u (set l0 v x)) = v,  from snd of view_set of product l1 l0 *)
  pose proof (f_equal snd (view_set hp10 (u, v) x)) as Hiv; simpl in Hiv.
  (* (v): set l0 v (set l1 u (set l0 v x)) = set l1 u (set l0 v x) *)
  pose proof (set_view hl0 (set l1 u (set l0 v x))) as Hsv0.
  rewrite Hiv in Hsv0.
  (* (C): set l0 v (set l1 u (set l0 v x)) = set l0 v (set l1 u x) *)
  pose proof (set_set hp01 (v, view l1 x) (v, u) x) as Hss01; simpl in Hss01.
  rewrite (set_view hl1 x) in Hss01.
  (* (v) and (C) share their LHS, so the RHSes are equal *)
  rewrite <- Hss01; exact Hsv0.
Qed.

End BothLawfulImpliesCommutative.

(*
Section LenticularRelationLaws.
  Context {a c : Type} (lr : Relational a a c c).

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
 *)
