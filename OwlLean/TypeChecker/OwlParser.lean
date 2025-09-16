import OwlLean.TypeChecker.OwlElaborator
import Lean
import Std.Data.HashMap

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

def TCtx := List String

def TCtx.lookup (t : TCtx) (s : String) : Option (Fin t.length) :=
  match t with
  | [] => .none
  | x::xs =>
    if x == s then .some ⟨0, by simp [List.length]⟩ else
      match TCtx.lookup xs s with
      | .none => .none
      | .some i => .some ⟨1 + i, by
        simp [List.length]
        omega⟩

-- test parser for labels
elab "label_parse" "(" p:owl_label ")" : term =>
    elabLabel p

def SLabel.elab (s : SLabel) (P : TCtx) : Option (Owl.label P.length) :=
  match s with
  | .var_label i =>
    match TCtx.lookup P i with
    | .none => .none
    | .some j => .some (label.var_label j)
  | .latl l => .some (label.latl l)
  | .lmeet l1 l2 =>
    match (SLabel.elab l1 P) with
    | .none => .none
    | .some l1' =>
      match (SLabel.elab l2 P) with
      | .none => .none
      | .some l2' => .some (label.lmeet l1' l2')
  | .ljoin l1 l2 =>
    match (SLabel.elab l1 P) with
    | .none => .none
    | .some l1' =>
      match (SLabel.elab l2 P) with
      | .none => .none
      | .some l2' => .some (label.ljoin l1' l2')
  | .embedlabel l => do
    let l' := (ren_label (shift_bound_by P.length) l)
    .some (Eq.symm (Nat.zero_add P.length) ▸ l')
  | .default => .some label.default

def SCondSym.elab (s : SCondSym) : Option Owl.cond_sym :=
  match s with
  | .leq => .some .leq
  | .geq => .some .geq
  | .lt => .some .lt
  | .gt => .some .gt
  | .nleq => .some .nleq
  | .ngeq => .some .ngeq
  | .nlt => .some .nlt
  | .ngt => .some .ngt

-- test parser for cond_sym
elab "cond_sym_parse" "(" p:owl_cond_sym ")" : term =>
    elabCondSym p

def SConstr.elab (s : SConstr) (P : TCtx) : Option (Owl.constr P.length) :=
  match s with
  | .condition cs l1 l2 =>
    match (SCondSym.elab cs) with
    | .none => .none
    | .some cs' =>
      match (SLabel.elab l1 P) with
      | .none => .none
      | .some l1' =>
        match (SLabel.elab l2 P) with
        | .none => .none
        | .some l2' => .some (.condition cs' l1' l2')

-- test parser for constraints
elab "constraint_parse" "(" p:owl_constr ")" : term =>
    elabConstr p

def SBinary.elab (s : SBinary) : Option Owl.binary :=
  match s with
  | .bend => .some .bend
  | .bzero b =>
      match (SBinary.elab b) with
      | .none => .none
      | .some b' => .some (.bzero b')
  | .bone b =>
      match (SBinary.elab b) with
      | .none => .none
      | .some b' => .some (.bone b')

-- test parser for binary
elab "binary_parse" "(" p:owl_binary ")" : term =>
    elabBinary p

def STy.elab (s : STy) (P : TCtx) (D : TCtx): Option (Owl.ty P.length D.length) :=
  match s with
  | .var_ty i =>
    match TCtx.lookup D i with
    | .none => .none
    | .some j => .some (ty.var_ty j)
  | .Any => .some ty.Any
  | .Unit => .some ty.Unit
  | .Data l =>
      match (SLabel.elab l P) with
      | .none => .none
      | .some l' => .some (ty.Data l')
  | .Ref t =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (ty.Ref t')
  | .arr t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.arr t1' t2')
  | .prod t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.prod t1' t2')
  | .sum t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.sum t1' t2')
  | .all a t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P (a::D)) with
          | .none => .none
          | .some t2' => .some (ty.all t1' t2')
  | .ex a t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P (a::D)) with
          | .none => .none
          | .some t2' => .some (ty.ex t1' t2')
  | .all_l s c l t =>
      match (SCondSym.elab c) with
      | .none => .none
      | .some c' =>
          match (SLabel.elab l P) with
          | .none => .none
          | .some l'=>
              match (STy.elab t (s::P) D) with
              | .none => .none
              | .some t' => .some (ty.all_l c' l' t')
  | .t_if c t1 t2 =>
      match (SConstr.elab c P) with
      | .none => .none
      | .some c' =>
        match (STy.elab t1 P D) with
        | .none => .none
        | .some t1' =>
            match (STy.elab t2 P D) with
            | .none => .none
            | .some t2' => .some (ty.t_if c' t1' t2')
  | .embedty t => do
    let t' := (ren_ty (shift_bound_by P.length) (shift_bound_by D.length) t)
    .some (Eq.symm (Nat.zero_add D.length) ▸
          Eq.symm (Nat.zero_add P.length) ▸ t')
  | .default => .some ty.default

-- test parser for types
elab "type_parse" "(" p:owl_type ")" : term =>
    elabType p

def SExpr.elab (s : SExpr) (P : TCtx) (D : TCtx) (G : TCtx): Option (Owl.tm P.length D.length G.length) :=
  match s with
  | .var_tm i =>
    match TCtx.lookup G i with
    | .none => .none
    | .some j => .some (tm.var_tm j)
  | .error => .some tm.error
  | .skip => .some tm.skip
  | .bitstring b =>
    match (SBinary.elab b) with
    | .none => .none
    | .some b' => .some (tm.bitstring b')
  | .loc n => .some (tm.loc n)
  | .fixlam f x e =>
    match (SExpr.elab e P D (f::x::G)) with
    | .none => .none
    | .some e' => .some (tm.fixlam e')
  | .tlam t e =>
    match (SExpr.elab e P (t::D) G) with
    | .none => .none
    | .some e' => .some (tm.tlam e')
  | .l_lam l e =>
    match (SExpr.elab e (l::P) D G) with
    | .none => .none
    | .some e' => .some (tm.l_lam e')
  | .Op op e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.Op op e1' e2')
  | .embedtm e => do
    let e' := (ren_tm (shift_bound_by P.length) (shift_bound_by D.length) (shift_bound_by G.length) e)
    .some (Eq.symm (Nat.zero_add G.length) ▸
          Eq.symm (Nat.zero_add D.length) ▸
          Eq.symm (Nat.zero_add P.length) ▸ e')
  | .zero e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.zero e')
  | .app e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.app e1' e2')
  | .alloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.alloc e')
  | .dealloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.dealloc e')
  | .assign e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.assign e1' e2')
  | .tm_pair e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.tm_pair e1' e2')
  | .left_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.left_tm e')
  | .right_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.right_tm e')
  | .inl e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.inl e')
  | .inr e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.inr e')
  | .case e x1 e1 x2 e2 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P D (x1::G)) with
      | .none => .none
      | .some e1' =>
        match (SExpr.elab e2 P D (x2::G)) with
        | .none => .none
        | .some e2' => .some (tm.case e' e1' e2')
  | .tapp e t =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (tm.tapp e' t')
  | .lapp e l =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SLabel.elab l P) with
      | .none => .none
      | .some l' => .some (tm.lapp e' l')
  | .pack e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.pack e')
  | .unpack e a x e1 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P (a::D) (x::G)) with
      | .none => .none
      | .some e1' => .some (tm.unpack e' e1')
  | .if_tm e1 e2 e3 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SExpr.elab e3 P D G) with
        | .none => .none
        | .some e3' => .some (tm.if_tm e1' e2' e3')
  | .if_c c e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SConstr.elab c P) with
        | .none => .none
        | .some c' => .some (tm.if_c c' e1' e2')
  | .sync e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.sync e')
  | .default => .some tm.default

-- test parser for terms
elab "term_parse" "(" p:owl_tm ")" : term =>
    elabTm p

-- check that terms works
elab "Owl_Parse" "{" p:owl_tm "}" : term => do
    elabTm p

def elabHelperTy (s : STy) : ty 0 0 :=
  match STy.elab s [] [] with
  | .some e => e
  | .none => ty.Any --default value

def elabHelper (s : SExpr) : tm 0 0 0 :=
  match SExpr.elab s [] [] [] with
  | .some e => e
  | .none => tm.skip --default value

open Lean Elab Meta

elab "Owl" "{" p:owl_tm "}" : term => do
  let sexprTerm ← elabTm p
  let sexprTerm2 ← elabTm_closed p
  let sVal : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm2
    match SExpr.elab sVal [] [] [] with
    | .none   => throwError "owl: ill-formed term"
    | .some _ => mkAppM ``elabHelper #[sexprTerm]

elab "OwlTy" "{" p:owl_type "}" : term => do
  let sexprTerm : Expr <- elabType p
  let sexprTerm2 ← elabType_closed p
  let sVal : STy <- (unsafe do Meta.evalExpr STy (mkConst ``STy) sexprTerm2)
    match STy.elab sVal [] [] with
    | .none => throwError "owl: ill-formed term"
    | .some _ => mkAppM ``elabHelperTy #[sexprTerm]
