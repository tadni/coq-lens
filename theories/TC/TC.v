From Coq.Classes Require Import DecidableClass.
From Coq.Lists Require Import List.
From Coq.Strings Require Import String.
From MetaCoq.Utils Require Import utils monad_utils.
From MetaCoq.Template Require Import Ast Loader TemplateMonad.
From Lens Require Import Lens.

Import MCMonadNotation.

Set Primitive Projections.

Record Info := {
  type   : ident;
  ctor   : ident;
  fields : list projection_body;
  npars  : nat;
  params : list context_decl;
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Definition lensName (ls : String.string) (i : ident) : ident :=
  String.of_string (ls ++ String.to_string i).

MetaCoq Quote Definition cBuild_Polymorphic := Build_Polymorphic.

Local Definition mkLens (At : term) (info : Info) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let np      := info.(npars) in
    let ps      := info.(params) in
    let fields  := info.(fields) in
    let nfields := List.length fields in
    let param_args := map tRel (rev (countTo np)) in
    let AppliedAt :=
      if Nat.eqb np 0 then At
      else tApp At param_args
    in
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some body =>
      let name := body.(proj_name) in
      let Bt := subst1 (tRel 0) 0 body.(proj_type) in
      let p (x : nat) : projection := mkProjection ind np x in
      let param_ctor_args := map (fun k => tRel (k + 2)) (rev (countTo np)) in
      let get_body := tProj (p i) (tRel 0) in
      (* set: tRel 1 = new value, tRel 0 = record p *)
      let f x :=
        if PeanoNat.Nat.eqb x i
        then tRel 1          (* the new value directly *)
        else tProj (p x) (tRel 0)
      in
      let update_body :=
        tApp ctor (param_ctor_args ++ map f (countTo nfields))
      in
      let lens_body :=
        tApp cBuild_Polymorphic (
          AppliedAt :: AppliedAt :: Bt :: Bt ::
          tLambda (mkBindAnn nAnon Relevant) AppliedAt get_body ::
          (* set: λ (new : Bt) (p : AppliedAt), update_body *)
          tLambda (mkBindAnn nAnon Relevant) Bt
            (tLambda (mkBindAnn nAnon Relevant) (lift 1 0 AppliedAt) update_body) ::
          nil)
      in
      let wrapped :=
        fold_right
          (fun decl acc => tLambda decl.(decl_name) decl.(decl_type) acc)
          lens_body
          (rev ps)
      in
      Some (lensName "_" name, wrapped)
    end
  | _ => None
  end.

Fixpoint get_arity (t : term) : nat :=
  match t with
  | tProd _ _ t => S (get_arity t)
  | _ => 0
  end.

Local Definition getFields (mi : mutual_inductive_body) (n : nat) : TemplateMonad Info :=
  match nth_error mi.(ind_bodies) n with
  | None => tmFail "no body for index"
  | Some oib =>
    match oib.(ind_ctors) with
    | nil => tmFail "`getFields` got empty type"
    | ctor :: nil =>
      let ctor_name := ctor.(cstr_name) in
      let ctor_type := ctor.(cstr_type) in
      match oib.(ind_projs) with
      | nil =>
        let ctor_arity := get_arity ctor_type in
        if decide (ctor_arity > get_arity oib.(ind_type)) then
          let name := String.to_string ctor_name in
          let arity := String.to_string (MCString.string_of_nat ctor_arity) in
          tmFail (String.of_string (
            "info: the constructor " ++ name ++ " has no projections but " ++
            "an arity of " ++ arity ++ ". Perhaps you forgot to enable " ++
            "primitive projections before the definition of the Record."
          )%string)
        else ret tt
      | _ => ret tt
      end ;;
      ret {|
        type   := oib.(ind_name) ;
        ctor   := ctor_name ;
        fields := oib.(ind_projs) ;
        npars  := mi.(ind_npars) ;
        params := mi.(ind_params) ;
      |}
    | _ => tmFail "`getFields` got variant type"
    end
  end.

Local Definition genLensCore (info : Info) (ty : term) : TemplateMonad unit :=
  let gen i :=
    match mkLens ty info i with
    | None   => tmFail "failed to build lens"
    | Some l => '(n, d) <- tmEval cbv l ;; tmMkDefinition n d
    end
  in
  monad_iter gen (countTo (List.length info.(fields))).

Definition genLens (T : Type) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  i  <- match ty with tInd i _ => ret i | _ => tmFail "given type is not inductive" end ;;
  let name := i.(inductive_mind) in
  ind <- tmQuoteInductive name ;;
  info <- getFields ind i.(inductive_ind) ;;
  genLensCore info ty.

Definition genLensK (baseName : kername) : TemplateMonad unit :=
  let inductive :=
    {| inductive_mind := baseName; inductive_ind := 0 |}
  in
  let ty := Ast.tInd inductive List.nil in
  ind <- tmQuoteInductive baseName ;;
  info <- getFields ind 0 ;;
  genLensCore info ty.

Definition genLensN (name : qualid) : TemplateMonad unit :=
  refs <- tmLocate name ;;
  match refs with
  | IndRef ind :: _ =>
    let ty := Ast.tInd ind List.nil in
    mi <- tmQuoteInductive ind.(inductive_mind) ;;
    info <- getFields mi ind.(inductive_ind) ;;
    genLensCore info ty
  | [] => tmFail ("not found")
  | _ => tmFail ("not an inductive")
  end.
