From Coq Require Setoids.Setoid.

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

Definition coproduct {a c c' : Type}
           (l0 : Simple a c) (l1 : Simple a c')
           : Simple a (c * c') :=
{| view := fun x : a => (view l0 x, view l1 x)
 ; set := fun (p : c * c') (x : a) =>
   let '(u, v) := p in
   set l0 u (set l1 v x) |}.

Definition over {a b c d : Type} (l : Polymorphic a b c d) (f : c -> d) : a -> b :=
  fun x => set l (f (view l x)) x.

Record Lawful {a c : Type} (l : Simple a c) : Prop :=
  { view_set :
      (* Viewing what you just set gives back the new value *)
      forall (new : c) (x : a), view l (set l new x) = new
  ; set_view :
      (* Setting what you just viewed changes nothing *)
      forall (x : a), set l (view l x) x = x
  ; set_set  :
      (* Two sets at the same focus, last wins *)
      forall (u v : c) (x : a), set l v (set l u x) = set l v x
  }.
Arguments view_set {a c l}.
Arguments set_view {a c l}.
Arguments set_set {a c l}.

Definition commutative {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c') : Prop :=
  forall (x : a) (v : c) (u : c'),
    set l0 v (set l1 u x) = set l1 u (set l0 v x).

(* The view completely determines the source, present in bijective lenses *)
Definition strong_set_view {a c : Type} (l : Simple a c) : Prop :=
  forall (x x' : a),
    set l (view l x) x' = x.

(* over is determined by view and set *)
Definition over_spec' {a c : Type} (l : Simple a c) : Prop :=
  forall (f : c -> c) (x : a),
    over l f x = set l (f (view l x)) x.

Definition independent_view_set {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c') : Prop :=
  forall (x : a) (u : c'),
    view l0 (set l1 u x) = view l0 x.

Theorem lawful_composition {a c d : Type} {l0 : Simple a c} {l1 : Simple c d}
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) :
  Lawful (compose l0 l1).
Proof.
Admitted.

Theorem lawful_product {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c')
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (compatible : commutative l0 l1) :
  Lawful (coproduct l0 l1).
Proof.
  apply Build_Lawful.
  - intros [u v] x. simpl. f_equal.
    + apply (view_set lawful0).
    + rewrite compatible. apply (view_set lawful1).
  - intros x. simpl. rewrite (set_view lawful1).
    apply (set_view lawful0). 
  - intros [u u'] [v v'] x. simpl.
    rewrite <- compatible. rewrite (set_set lawful1). rewrite (set_set lawful0).
    reflexivity.
Qed.

Theorem commutative_independent {a c c' : Type} {l0 : Simple a c} {l1 : Simple a c'}
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (compatible : commutative l0 l1) :
  independent_view_set l0 l1.
Proof.
  unfold commutative in compatible.
  unfold independent_view_set. intros x u.
  rewrite <- (set_view lawful0 x) at 1.
  rewrite <- compatible. apply (view_set lawful0).
Qed.

Theorem commutative_symmetric {a c c' : Type} {l0 : Simple a c} {l1 : Simple a c'}
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (compatible : commutative l0 l1) :
  commutative l1 l0.
Proof.
  unfold commutative in *.
  intros. symmetry. apply compatible.
Qed.

Definition equivalent {a d : Type}
  (l0 : Simple a d) (l1 : Simple a d) : Prop :=
  (forall x, view l0 x = view l1 x)
  /\ (forall v x, set l0 v x = set l1 v x).

Definition observed {a c d : Type}
  (smaller : Simple a c) (bigger : Simple a d) : Prop :=
  exists (witness : Simple d c), Lawful witness /\ equivalent smaller (compose bigger witness).

Definition join {a c c' d : Type}
  (l0 : Simple a c) (l1 : Simple a c') (l2 : Simple a d) : Prop :=
  (observed l0 l2) /\ (observed l1 l2)
  /\ (forall e (l3 : Simple a e),
       (observed l0 l3 /\ observed l1 l3) -> observed l2 l3).

Theorem exists_join {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c')
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (compatible : commutative l0 l1) :
  exists (d : Type) (l2 : Simple a d), join l0 l1 l2.
Proof.
Admitted.

Theorem observed_independent {a b c d : Type}
  (l0 : Simple a b) (l1 : Simple a c) (l2 : Simple a d)
  (lawful0 : Lawful l0) (lawful1 : Lawful l1) (lawful2 : Lawful l2)
  (bounded : observed l0 l1) (compatible : commutative l1 l2) : commutative l0 l2.
Proof.
  unfold commutative. intros x v u.
  unfold observed in bounded.
  destruct bounded as [witness [lawful_witness l0_to_l1]].
  apply proj2 in l0_to_l1.
  rewrite l0_to_l1. rewrite l0_to_l1.
  simpl. rewrite (commutative_independent lawful1 lawful2 compatible).
  rewrite compatible. reflexivity.
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

(* The coproduct view is (a,b)↦(a,b) and setter ignores the old value entirely,
   so it is the full-replacement (bijective) lens on option bool * bool *)
Lemma lawful_product_l0_l1 : Lawful (coproduct l0 l1).
Proof.
  constructor.
  - intros [u v] [a b]; reflexivity.
  - intros [a b]; destruct a as [[]|], b; reflexivity.
  - intros [u u'] [v v'] [a b]; reflexivity.
Qed.

Lemma not_lawful_product_l1_l0 : ~ Lawful (coproduct l1 l0).
Proof.
  intro H.
  specialize (view_set H (true, None) (None, false)).
  simpl; discriminate.
Qed.

(* The coproduct is also bijective: setting the viewed value gives the same result
   regardless of the starting point *)
Lemma strong_set_view_product : strong_set_view (coproduct l0 l1).
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
Context (hp01 : Lawful (coproduct l0 l1)) (hp10 : Lawful (coproduct l1 l0)).

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
  (* view l0 (set l1 u (set l0 v x)) = v,  from snd of view_set of coproduct l1 l0 *)
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

Definition to_relational {a b c d : Type} (l : Polymorphic a b c d) : Relational a b c d :=
  {| r_view := fun x y => view l x = y
   ; r_set  := fun v x y => set l v x = y
  |}.

Definition RelationalSimple (a c : Type) : Type := Relational a a c c.

Definition relational_compose {a b c d e f : Type}
    (l0 : Relational a b c d) (l1 : Relational c d e f)
    : Relational a b e f :=
  {| r_view := fun (x : a) (z : e) =>
       exists (y : c), r_view l0 x y /\ r_view l1 y z
   ; r_set  := fun (u : f) (x : a) (y : b) =>
       exists (v : d),
         (exists (w : c), r_view l0 x w /\ r_set l1 u w v)
         /\ r_set l0 v x y
  |}.

Definition relational_product {a c c' : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c')
    : RelationalSimple a (c * c') :=
  {| r_view := fun (x : a) (p : c * c') =>
       r_view l0 x (fst p) /\ r_view l1 x (snd p)
   ; r_set  := fun (p : c * c') (x y : a) =>
       exists (mid : a), r_set l1 (snd p) x mid /\ r_set l0 (fst p) mid y
  |}.

Definition relational_over {a b c d : Type}
    (l : Relational a b c d) (f : c -> d -> Prop) : a -> b -> Prop :=
  fun x y => exists u v, r_view l x u /\ f u v /\ r_set l v x y.

Record RelationalLawful {a c : Type} (l : RelationalSimple a c) : Prop :=
  { relational_view_set :
      (* Setting to a focus makes that focus a possible view of the result *)
      forall (focus : c) (source result : a),
        r_set l focus source result -> r_view l result focus
  ; relational_set_view :
      (* Setting a focus you can already view leaves the source reachable *)
      forall (source : a) (focus : c),
        r_view l source focus -> r_set l focus source source
  ; relational_set_set :
      (* Two sequential sets: the intermediate focus is irrelevant *)
      forall (focus focus' : c) (x y z : a),
        r_set l focus x y -> r_set l focus' y z -> r_set l focus' x z
  }.
Arguments relational_view_set {a c l}.
Arguments relational_set_view {a c l}.
Arguments relational_set_set {a c l}.

(* The possible two-step results are order-independent *)
Definition relational_commutative {a c c' : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c') : Prop :=
  forall (origin terminus : a) (focus : c) (focus' : c'),
    (exists (mid : a), r_set l1 focus' origin mid /\ r_set l0 focus mid terminus) <->
    (exists (mid : a), r_set l0 focus origin mid /\ r_set l1 focus' mid terminus).

(* The view alone determines the whole source, as in bijective lenses *)
Definition relational_strong_set_view {a c : Type} (l : RelationalSimple a c) : Prop :=
  forall (source anchor : a) (focus : c),
    r_view l source focus -> r_set l focus anchor source.

(* relational_over is determined by r_view and r_set — holds by definition *)
Definition relational_over_specification {a c : Type} (l : RelationalSimple a c) : Prop :=
  forall (f : c -> c -> Prop) (x y : a),
    relational_over l f x y <-> exists u v, r_view l x u /\ f u v /\ r_set l v x y.

(* Setting through l1 carries l0-views forward from source to result *)
Definition relational_independent_view_set {a c c' : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c') : Prop :=
  forall (source result : a) (focus' : c') (focus : c),
    r_set l1 focus' source result -> r_view l0 source focus -> r_view l0 result focus.

Theorem relational_lawful_composition {a c d : Type}
    {l0 : RelationalSimple a c} {l1 : RelationalSimple c d}
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1) :
    RelationalLawful (relational_compose l0 l1).
Proof.
Admitted.

Theorem relational_lawful_product {a c c' : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c')
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1)
    (compatible : relational_commutative l0 l1) :
    RelationalLawful (relational_product l0 l1).
Proof.
  apply Build_RelationalLawful.
  - intros [focus focus'] source result [mid [Hset1 Hset0]]; simpl in *.
    split.
    + exact (relational_view_set lawful0 focus mid result Hset0).
    + destruct (proj1 (compatible source result focus focus')
                  (ex_intro _ mid (conj Hset1 Hset0))) as [mid' [_ Hset1']].
      exact (relational_view_set lawful1 focus' mid' result Hset1').
  - intros source [focus focus'] [Hview0 Hview1]; simpl in *.
    exact (ex_intro _ source
            (conj (relational_set_view lawful1 source focus' Hview1)
                  (relational_set_view lawful0 source focus Hview0))).
  - intros [focus focus'] [focus'' focus'''] x y z
           [mid  [Hset1u Hset0u]]
           [mid' [Hset1v Hset0v]]; simpl in *.
    (* Commute the inner l0/l1 sets to untangle the four-step chain *)
    destruct (proj2 (compatible mid mid' focus focus''')
                (ex_intro _ y (conj Hset0u Hset1v))) as [mid'' [Hcomm1 Hcomm0]].
    exact (ex_intro _ mid''
            (conj (relational_set_set lawful1 focus' focus''' x mid mid'' Hset1u Hcomm1)
                  (relational_set_set lawful0 focus focus'' mid'' mid' z Hcomm0 Hset0v))).
Qed.

Theorem relational_commutative_independent {a c c' : Type}
    {l0 : RelationalSimple a c} {l1 : RelationalSimple a c'}
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1)
    (compatible : relational_commutative l0 l1) :
    relational_independent_view_set l0 l1.
Proof.
  unfold relational_independent_view_set.
  intros source result focus' focus Hset Hview.
  (* Reflect Hview into a set, then commute to get a set ending at result *)
  destruct (proj2 (compatible source result focus focus')
              (ex_intro _ source
                (conj (relational_set_view lawful0 source focus Hview) Hset)))
    as [mid [_ Hmid0]].
  exact (relational_view_set lawful0 focus mid result Hmid0).
Qed.

Theorem relational_commutative_symmetric {a c c' : Type}
    {l0 : RelationalSimple a c} {l1 : RelationalSimple a c'}
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1)
    (compatible : relational_commutative l0 l1) :
    relational_commutative l1 l0.
Proof.
  unfold relational_commutative in *.
  intros origin terminus focus focus'.
  exact (iff_sym (compatible origin terminus focus' focus)).
Qed.

Definition relational_equivalent {a d : Type}
    (l0 : RelationalSimple a d) (l1 : RelationalSimple a d) : Prop :=
  (forall (x : a) (y : d), r_view l0 x y <-> r_view l1 x y)
  /\ (forall (focus : d) (x y : a), r_set l0 focus x y <-> r_set l1 focus x y).

Definition relational_observed {a c d : Type}
    (smaller : RelationalSimple a c) (bigger : RelationalSimple a d) : Prop :=
  exists (witness : RelationalSimple d c),
    RelationalLawful witness
    /\ relational_equivalent smaller (relational_compose bigger witness).

Definition relational_join {a c c' d : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c') (l2 : RelationalSimple a d) : Prop :=
  relational_observed l0 l2
  /\ relational_observed l1 l2
  /\ forall e (l3 : RelationalSimple a e),
       relational_observed l0 l3 /\ relational_observed l1 l3 -> relational_observed l2 l3.

Theorem relational_exists_join {a c c' : Type}
    (l0 : RelationalSimple a c) (l1 : RelationalSimple a c')
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1)
    (compatible : relational_commutative l0 l1) :
    exists (d : Type) (l2 : RelationalSimple a d), relational_join l0 l1 l2.
Proof.
Admitted.

Theorem relational_observed_independent {a b c d : Type}
    (l0 : RelationalSimple a b) (l1 : RelationalSimple a c) (l2 : RelationalSimple a d)
    (lawful0 : RelationalLawful l0) (lawful1 : RelationalLawful l1) (lawful2 : RelationalLawful l2)
    (bounded : relational_observed l0 l1) (compatible : relational_commutative l1 l2) :
    relational_commutative l0 l2.
Proof.
Admitted.

Theorem lawful_to_relational {a c : Type} (l : Simple a c) (lawful : Lawful l) :
    RelationalLawful (to_relational l).
Proof.
  apply Build_RelationalLawful; simpl.
  - (* relational_view_set: set l focus source = result → view l result = focus *)
    intros focus source result Hset.
    rewrite <- Hset. apply (view_set lawful).
  - (* relational_set_view: view l source = focus → set l focus source = source *)
    intros source focus Hview.
    rewrite <- Hview. apply (set_view lawful).
  - (* relational_set_set: set l focus x = y → set l focus' y = z → set l focus' x = z *)
    intros focus focus' x y z Hset Hset'.
    rewrite <- Hset', <- Hset. symmetry. apply (set_set lawful).
Qed.

Theorem commutative_to_relational {a c c' : Type} (l0 : Simple a c) (l1 : Simple a c')
    (compatible : commutative l0 l1) :
    relational_commutative (to_relational l0) (to_relational l1).
Proof.
  unfold relational_commutative; simpl.
  intros origin terminus focus focus'. split.
  - intros [mid [Hset1 Hset0]].
    exists (set l0 focus origin). split; [reflexivity|].
    rewrite <- Hset0, <- Hset1. symmetry. apply compatible.
  - intros [mid [Hset0 Hset1]].
    exists (set l1 focus' origin). split; [reflexivity|].
    rewrite <- Hset1, <- Hset0. apply compatible.
Qed.
