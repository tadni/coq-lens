From Lens Require Import Lens.
From Lens.TC Require Import TC.
From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import utils monad_utils.

Import MCMonadNotation.

Set Primitive Projections.

Record Pair (A B : Type) := {
  fst' : A ;
  snd' : B ;
}.
MetaCoq Run (genLensK (MPfile ["test"], "Pair")).
Arguments fst' {_ _}.
Arguments snd' {_ _}.
Arguments _fst' {_ _}.
Arguments _snd' {_ _}.
(* Check the types of the generated lenses *)
About _fst'.
About _snd'.

(* Basic view tests *)
Example view_fst : view _fst' {| fst' := 1 ; snd' := true |} = 1.
Proof. reflexivity. Qed.

Example view_snd : view _snd' {| fst' := 1 ; snd' := true |} = true.
Proof. reflexivity. Qed.

(* Basic over tests *)
Example over_fst : over _fst' S {| fst' := 1 ; snd' := true |} = {| fst' := 2 ; snd' := true |}.
Proof. reflexivity. Qed.

Example over_snd : over _snd' negb {| fst' := 1 ; snd' := true |} = {| fst' := 1 ; snd' := false |}.
Proof. reflexivity. Qed.

(* set is over with a constant function *)
Example set_fst : over _fst' (fun _ => 42) {| fst' := 1 ; snd' := true |} = {| fst' := 42 ; snd' := true |}.
Proof. reflexivity. Qed.

(* view after over gives the result of the function *)
Example view_over_fst (p : Pair nat bool) (f : nat -> nat) :
  view _fst' (over _fst' f p) = f (view _fst' p).
Proof. reflexivity. Qed.

(* over on one field doesn't affect the other *)
Example over_fst_snd_independent (p : Pair nat bool) (f : nat -> nat) :
  view _snd' (over _fst' f p) = view _snd' p.
Proof. reflexivity. Qed.

Example over_snd_fst_independent (p : Pair nat bool) (f : bool -> bool) :
  view _fst' (over _snd' f p) = view _fst' p.
Proof. reflexivity. Qed.

(* over twice composes *)
Example over_twice (p : Pair nat bool) (f g : nat -> nat) :
  over _fst' f (over _fst' g p) = over _fst' (fun x => f (g x)) p.
Proof. reflexivity. Qed.

(* lens composition *)
Record Nested (A : Type) := {
  inner : Pair A bool ;
}.
MetaCoq Run (genLensK (MPfile ["test"], "Nested")).
Arguments inner {_}.
Arguments _inner {_}.

Example view_composed (n : Nested nat) :
  view (lens_compose _inner _fst') n = view _fst' (view _inner n).
Proof. reflexivity. Qed.
