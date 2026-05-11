import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.TcSimple
import OwlLean.TypeChecker.OwlScopedContext
import OwlLean.OwlLang.Owl
import OwlLean.TypeChecker.OwlTyping

open Lean Elab Meta
open Owl

declare_syntax_cat owl_var
declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_constr
declare_syntax_cat owl_cond_sym
-- declare_syntax_cat owl_phi
-- declare_syntax_cat owl_phi_entry
declare_syntax_cat owl_delta
declare_syntax_cat owl_gamma
declare_syntax_cat owl_delta_entry
declare_syntax_cat owl_gamma_entry
declare_syntax_cat owl_psi_entry
declare_syntax_cat owl_psi
declare_syntax_cat owl_rexp
declare_syntax_cat owl_decl_entry
declare_syntax_cat owl_decl

private def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => none

private def tyParamNats (ty : Expr) : MetaM (ScopeMap 3) := do
  let ty ← whnf ty
  unless ty.getAppFn.isConstOf ``Owl.ty do
    throwError s!"expected Owl.ty …, got {ty}"
  let a := ty.getAppArgs
  unless 1 ≤ a.size do throwError s!"ty application too small: {ty} got {a.size} argu"
  let s := a[0]!
  unsafe evalExpr (ScopeMap 3) (mkApp (mkConst ``ScopeMap) (mkNatLit 3)) s

private def labelParamNat (ty : Expr) : MetaM Nat := do
  let ty ← whnf ty
  unless ty.getAppFn.isConstOf ``Owl.label do
    throwError s!"expected Owl.label …, got {ty}"
  let a := ty.getAppArgs
  unless 1 ≤ a.size do throwError s!"label application too small"
  match natLit? a[0]! with
  | some n => return n
  | none => throwError s!"label index not a nat literal: {ty}"

-- syntax for variables
syntax ident : owl_var
syntax "_" : owl_var

-- syntax for labels
syntax ident : owl_label
syntax "⟨" term "⟩"  : owl_label
syntax "⊥" : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "$" term:max "[" owl_label,* "]" : owl_label
syntax "$" term:max : owl_label
syntax "(" owl_label ")" : owl_label

partial def elabVar : Syntax → String
  | `(owl_var| $id:ident) => id.getId.toString
  | _ => "unused variable"


def subst_label (l : label (ScopeMap.ofList [x])) (f : Fin x -> label r) : label r  :=
  let s : LabelSubst (ScopeMap.ofList [x]) r := ⟨fun j i =>
    match j with
    | 0 => f i⟩
  l.subst s

def subst_ty (T : ty (ScopeMap.ofList [l, r, t]))
   (f : Fin l -> label (ScopeMap.ofList [l']))
   (g : Fin r -> rexp (ScopeMap.ofList [l', r']))
   (h : Fin t -> ty (ScopeMap.ofList [l', r', t'])) :
   ty (ScopeMap.ofList [l', r', t']) :=
   T.subst $ ⟨fun j i =>
     match j with
     | 0 => f i
     | 1 => g i
     | 2 => h i
    ⟩

partial def elabLabel (stx : Syntax) (P : TCtx := []) : TermElabM (label (ScopeMap.ofList [P.length])) :=
  match stx with
  | `(owl_label| ( $e:owl_label)) => elabLabel e P
  | `(owl_label| ⟨ $t:term ⟩ ) => do
      let tEx ← Term.elabTerm t (mkConst ``Owl.LabelTm)
      let tTy ← instantiateMVars (← inferType tEx)
      let tVal ← unsafe Meta.evalExpr (α := Owl.LabelTm) tTy tEx
      return .latl tVal
  | `(owl_label| $e1:owl_label ⊔ $e2:owl_label) => do
      let e1 ← elabLabel e1 P
      let e2 ← elabLabel e2 P
      return .ljoin e1 e2
  | `(owl_label| $e1:owl_label ⊓ $e2:owl_label) => do
      let e1 ← elabLabel e1 P
      let e2 ← elabLabel e2 P
      return .lmeet e1 e2
  | `(owl_label| $id:ident) => do
      let nm := id.getId.toString
      match P.lookup nm with
      | .none => throwError s!"Unknown label variable: {nm}"
      | .some j => return .var_label nm j
  | `(owl_label| $ $l:term [ $xs:owl_label,* ] ) => do
      let xsVals ← xs.getElems.mapM (elabLabel · P)
      let xsList := xsVals.toList
      let lEx ← Term.elabTerm l (mkConst ``Owl.label)
      let lTy ← instantiateMVars (← inferType lEx)
      let lLen ← liftM <| labelParamNat lTy
      if h : lLen = xsList.length then
        let lVal ← liftM <| unsafe Meta.evalExpr (α := Owl.label (ScopeMap.ofList [lLen])) lTy lEx
        return subst_label lVal (h ▸ (xsList.get))
      else throwError s!"embedlabel: length mismatch: expected {lLen}, got {xsList.length}"
  | `(owl_label| $ $l:term ) => do
      let xsVals : List (label (ScopeMap.ofList [P.length])) := []
      let lEx ← Term.elabTerm l (mkConst ``Owl.label)
      let lTy ← instantiateMVars (← inferType lEx)
      let lLen ← liftM <| labelParamNat lTy
      if h0 : lLen = 0 then
        let lVal ← liftM <| unsafe Meta.evalExpr (α := Owl.label (ScopeMap.ofList [lLen])) lTy lEx
        have hx : xsVals.length = 0 := by simp [xsVals]
        have hlen : lLen = xsVals.length := h0.trans hx.symm
        return subst_label lVal (hlen ▸ (xsVals.get))
      else throwError "embedlabel: empty arg list but embedded label is not arity 0"
  | `(owl_label| ⊥) => return .latl Owl.LabelTm.bot
  | _ => throwUnsupportedSyntax

-- syntax for cond symbols
syntax "⊑" : owl_cond_sym
syntax "⊒" : owl_cond_sym
syntax "⊏" : owl_cond_sym
syntax "⊐" : owl_cond_sym
syntax "!⊑" : owl_cond_sym
syntax "!⊒" : owl_cond_sym
syntax "!⊏" : owl_cond_sym
syntax "!⊐" : owl_cond_sym

partial def elabCondSym : Syntax → TermElabM cond_sym
  | `(owl_cond_sym| ⊑) => return .leq
  | `(owl_cond_sym| ⊒) => return .geq
  | `(owl_cond_sym| ⊏) => return .lt
  | `(owl_cond_sym| ⊐) => return .gt
  | `(owl_cond_sym| !⊑) => return .nleq
  | `(owl_cond_sym| !⊒) => return .ngeq
  | `(owl_cond_sym| !⊏) => return .nlt
  | `(owl_cond_sym| !⊐) => return .ngt
  | _ => throwUnsupportedSyntax

-- syntax for contraints
syntax "(" owl_constr ")" : owl_constr
syntax owl_label owl_cond_sym owl_label : owl_constr

partial def elabConstr (stx : Syntax) (P : TCtx := []) : TermElabM (constr (ScopeMap.ofList [P.length])) :=
  match stx with
  | `(owl_constr| ( $e:owl_constr)) => elabConstr e P
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let l1 ← elabLabel l1 P
      let l2 ← elabLabel l2 P
      let c ← elabCondSym c
      return .condition c l1 l2
  | _ => throwUnsupportedSyntax


syntax ident : owl_rexp
syntax ident "(" owl_rexp "," owl_rexp ")" : owl_rexp
syntax ident "(" owl_rexp ")" : owl_rexp
syntax str : owl_rexp


partial def elab_rexp (stx : Syntax) (P : TCtx := []) (Rs : TCtx) : TermElabM (rexp (ScopeMap.ofList [P.length, Rs.length])) :=
  match stx with
  | `(owl_rexp | $op:ident ( $e1, $e2 )) => do
    let r1 ← elab_rexp e1 P Rs
    let r2 ← elab_rexp e2 P Rs
    return .binop op.getId.toString r1 r2
  | `(owl_rexp | $op:ident ( $e1 )) => do
    let r1 ← elab_rexp e1 P Rs
    return .unop op.getId.toString r1
  | `(owl_rexp | $i:ident ) => do
    let nm := i.getId.toString
    match Rs.lookup nm with
    | .none => throwError s!"Unknown refinement variable: {nm}"
    | .some j => return .var j
  | `(owl_rexp |  $ob:str  ) => do
    return .const ob.getString
  | _ => throwUnsupportedSyntax


declare_syntax_cat owl_prop
syntax "(" owl_prop ")" : owl_prop
syntax owl_rexp "=" owl_rexp : owl_prop
syntax owl_prop "∧" owl_prop : owl_prop
syntax owl_prop "∨" owl_prop : owl_prop
syntax owl_prop "→" owl_prop : owl_prop
syntax "¬" owl_prop : owl_prop
syntax "∀" ident "." owl_prop : owl_prop

partial def elab_prop (stx : Syntax) (P : TCtx) (Rs : TCtx)  : TermElabM (prop (ScopeMap.ofList [P.length, Rs.length])) :=
  match stx with
  | `(owl_prop| ( $e:owl_prop )) => elab_prop e P Rs
  | `(owl_prop| $e1:owl_rexp = $e2:owl_rexp) => do
    let r1 ← elab_rexp e1 P Rs
    let r2 ← elab_rexp e2 P Rs
    return .peq r1 r2
  | `(owl_prop| $p1:owl_prop ∧ $p2:owl_prop) => do
    let p1 ← elab_prop p1 P Rs
    let p2 ← elab_prop p2 P Rs
    return .pand p1 p2
  | `(owl_prop| $p1:owl_prop ∨ $p2:owl_prop) => do
    let p1 ← elab_prop p1 P Rs
    let p2 ← elab_prop p2 P Rs
    return .por p1 p2
  | `(owl_prop| $p1:owl_prop → $p2:owl_prop) => do
    let p1 ← elab_prop p1 P Rs
    let p2 ← elab_prop p2 P Rs
    return .pimpl p1 p2
  | `(owl_prop| ¬ $p:owl_prop) => do
    let p ← elab_prop p P Rs
    return .pnot p
  | `(owl_prop| ∀ $x:ident . $p:owl_prop ) => do
    let p ← elab_prop p P (x.getId.toString :: Rs)
    return .pall p
  | _ => throwUnsupportedSyntax

-- syntax for types
syntax "(" owl_type ")" : owl_type
syntax ident : owl_type
syntax "Any" : owl_type
syntax "unit" : owl_type
syntax "RData" owl_label "[" owl_rexp "]" : owl_type
syntax "Data" owl_label : owl_type
syntax "Ref" owl_type : owl_type
syntax "Maybe" owl_type : owl_type
syntax owl_type "->" owl_type : owl_type
syntax owl_type "*" owl_type : owl_type
syntax owl_type "+" owl_type : owl_type
syntax owl_type "∪" owl_type : owl_type
syntax owl_type "∩" owl_type : owl_type
syntax "∀" ident "<:" owl_type "." owl_type : owl_type
syntax "∃" ident "<:" owl_type "." owl_type : owl_type
syntax "∀" ident owl_cond_sym owl_label "." owl_type : owl_type
syntax "∃" ident "." owl_type : owl_type
syntax "∀" ident "." owl_type : owl_type
syntax "corr" "(" owl_label ")" "?" owl_type ":" owl_type : owl_type
syntax "Public" : owl_type
syntax "$" term:max "[" owl_label,* "]" "[" owl_rexp,* "]" "[" owl_type,* "]" : owl_type
syntax owl_type "{" owl_prop "}" : owl_type

partial def elabType (stx : Syntax) (P : TCtx) (Rs : TCtx) (D : TCtx) :
    TermElabM (ty (ScopeMap.ofList [P.length, Rs.length, D.length])) :=
  match stx with
  | `(owl_type| ( $e:owl_type)) => elabType e P Rs D
  | `(owl_type| $id:ident) => do
      let nm := id.getId.toString
      match D.lookup nm with
      | .none => throwError s!"Unknown type variable: {nm}"
      | .some j => return .var_ty j
  | `(owl_type| Any) => return .Any
  | `(owl_type| unit) => return .Unit
  | `(owl_type| Public) => return .Public
  | `(owl_type| Data $l:owl_label ) => do
    let l ← elabLabel l P
    return .Data l
  | `(owl_type| RData $l:owl_label [ $re ] ) => do
    let l ← elabLabel l P
    let r ← elab_rexp re P Rs
    return .RData l r
  | `(owl_type| Ref $t:owl_type) => do
    let t ← elabType t P Rs D
    return .Ref t
  | `(owl_type| Maybe $t:owl_type) => do
    elabType (← `(owl_type| $t + unit)) P Rs D
  | `(owl_type| $t1:owl_type -> $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    return .arr t1 t2
  | `(owl_type| $t1:owl_type * $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    return .prod t1 t2
  | `(owl_type| $t1:owl_type + $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    return .sum t1 t2
  | `(owl_type| $t1:owl_type ∪ $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    return .union t1 t2
  | `(owl_type| $t1:owl_type ∩ $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    return .inter t1 t2
  | `(owl_type| ∀ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs (id.getId.toString :: D)
    return .all t1 t2
  | `(owl_type| ∃ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs (id.getId.toString :: D)
    return .ex t1 t2
  | `(owl_type| ∃ $id:ident . $t2:owl_type) => do
    let t2 ← elabType t2 P (id.getId.toString :: Rs) D
    return .ex_r t2
  | `(owl_type| ∀ $id:ident . $t2:owl_type) => do
    let t2 ← elabType t2 P (id.getId.toString :: Rs) D
    return .all_r t2
  | `(owl_type| ∀ $id:ident $c:owl_cond_sym $l:owl_label . $t:owl_type) => do
    let c ← elabCondSym c
    let l ← elabLabel l P
    let t ← elabType t (id.getId.toString :: P) Rs D
    return .all_l c l t
  | `(owl_type| corr ( $c:owl_label ) ? $t1:owl_type : $t2:owl_type) => do
    let t1 ← elabType t1 P Rs D
    let t2 ← elabType t2 P Rs D
    let c ← elabLabel c P
    return .t_if c t1 t2
  | `(owl_type| $ $t:term [ $ls:owl_label,* ] [ $rs:owl_rexp,* ] [ $ts:owl_type,* ]) => do
    let lsVals ← ls.getElems.mapM (elabLabel · P)
    let lsList := lsVals.toList
    let tsVals ← ts.getElems.mapM (elabType · P Rs D)
    let tsValsL := tsVals.toList
    let rsVals ← rs.getElems.mapM (elab_rexp · P Rs)
    let rsValsL := rsVals.toList
    let tEx ← Term.elabTerm t (mkConst ``Owl.ty)
    let tTy ← instantiateMVars (← inferType tEx)
    let ty_s <- tyParamNats tTy
    if ty_s = ScopeMap.ofList [lsList.length, rsValsL.length, tsValsL.length] then
      let tVal ← liftM <| unsafe Meta.evalExpr (α := ty (ScopeMap.ofList [lsList.length, rsValsL.length, tsValsL.length])) tTy tEx
       return subst_ty tVal ((lsList.get)) (rsValsL.get) (tsValsL.get)
    else throwError s!"embedty: scope map mismatch"

--     let (llenInf, rlen, d_tyInf) ← liftM <| tyParamNats tTy
--     let llen := if llenInf = 0 && !lsList.isEmpty then lsList.length else llenInf
--     let d_ty := if d_tyInf = 0 && !tsValsL.isEmpty then tsValsL.length else d_tyInf
--     if llen = lsList.length then
--       if d_ty = tsValsL.length then
--         if rlen = Rs.length then
--           let tVal ← liftM <| unsafe Meta.evalExpr (α := ty (ScopeMap.ofList [lsList.length, Rs.length, tsValsL.length])) tTy tEx
--            return subst_ty tVal ((lsList.get))  (tsValsL.get)
--         else throwError s!"embedty: refinement length mismatch: expected {Rs.length}, got {rlen}"
--       else throwError s!"embedty: type arg mismatch: expected {d_ty}, got {tsValsL.length}"
--     else throwError s!"embedty: label arg mismatch: inferred head arity {llenInf}, splice has {lsList.length} label(s) (resolved llen := {llen})"
  | `(owl_type| $t:owl_type { $p }) => do
    let t ← elabType t P Rs D
    let p ← elab_prop p P Rs
    return .refined t p
  | _ => throwError "Unexpected syntax for elabType"

notation:100 "PURE" => pure ()
notation:100 "THROW" => throw ()

-- syntax for terms
syntax "(" owl_tm ")" : owl_tm
syntax ident : owl_tm
syntax num : owl_tm
syntax "error" : owl_tm
syntax "()" : owl_tm
syntax str : owl_tm
syntax "fix" owl_var "(" owl_var ")" owl_tm : owl_tm
syntax "Λ" owl_var "." owl_tm : owl_tm
syntax "Λβ" owl_var "." owl_tm : owl_tm
syntax "Λr" ident "." owl_tm : owl_tm
syntax "⟨" owl_tm "," owl_tm "⟩" : owl_tm
syntax "⟨" term "⟩" "(" owl_tm "," owl_tm ")" : owl_tm -- Binary Op case
syntax "⟨" term "⟩" "(" owl_tm ")" : owl_tm -- Unary Op case
syntax "zero" owl_tm : owl_tm
syntax owl_tm owl_tm : owl_tm
syntax "alloc" owl_tm : owl_tm
syntax "!" owl_tm : owl_tm
syntax owl_tm ":=" owl_tm : owl_tm
syntax "π1" owl_tm : owl_tm
syntax "π2" owl_tm : owl_tm
syntax "ı1" owl_tm : owl_tm
syntax "ı2" owl_tm : owl_tm
syntax "case" owl_tm "with" "|" "inl" owl_var "=>" owl_tm "|" "inr" owl_var "=>" owl_tm : owl_tm
syntax owl_tm "[" owl_type "]" : owl_tm
syntax owl_tm "[{" owl_rexp "}]" : owl_tm
syntax owl_tm "⟨" owl_label "⟩" : owl_tm
syntax "pack" "(" owl_type "," owl_tm ")" : owl_tm
syntax "rpack" "(" owl_rexp "," owl_tm ")" : owl_tm
syntax "unpack" owl_tm "as" "(" owl_var "," owl_var ")" "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" "corr" "(" owl_label ")" "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm
syntax "union_elim" ident "=" owl_tm "in" owl_tm : owl_tm
syntax "let" owl_var "=" owl_tm "in" owl_tm : owl_tm
syntax owl_tm ";" owl_tm : owl_tm
syntax "let" owl_var ":" owl_type "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "admit" owl_var ":" owl_type "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" owl_var "," owl_var ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" owl_var "," owl_var "," owl_var ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "λ" "(" owl_var ":" owl_type ")" ":" owl_type "=>" owl_tm : owl_tm
syntax "λ" owl_var "=>" owl_tm : owl_tm
syntax "$" term:max "[" owl_label,* "]" "[" owl_type,* "]" "[" owl_tm,* "]" : owl_tm
syntax "corr_case" owl_label "in" owl_tm : owl_tm
syntax "(" owl_tm ":" owl_type ")" : owl_tm
syntax owl_tm "." num : owl_tm
syntax "admit" : owl_tm

-- ALLOW : let (x , y) = e in ...
-- expands to :
-- let e' = e in
-- let x = π1 e' in
-- let y = π2 e' in ...

deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax

def mkOpaqueSyntax (s : Lean.Syntax) : Owl.opaqueSyntax := { inner := s }

mutual
  partial def elabTm (stx : Syntax) (P Rs D G : TCtx) : TermElabM (tm (ScopeMap.ofList [P.length, Rs.length, D.length, G.length])) := do
    let body ← elabTmX stx P Rs D G
    return .mk (mkOpaqueSyntax stx) body

  partial def elabTmX (stx : Syntax) (P Rs D G : TCtx) : TermElabM (tmX (ScopeMap.ofList [P.length, Rs.length, D.length, G.length])) :=
  match stx with
  | `(owl_tm| ( $e:owl_tm)) => elabTmX e P Rs D G
  | `(owl_tm| admit ) => return .admit
  | `(owl_tm| $id:ident) => do
      let nm := id.getId.toString
      match G.lookup nm with
      | .none => throwError s!"Unknown term variable: {nm}"
      | .some j => return .var_tm j
  | `(owl_tm| error) => return .error
  | `(owl_tm| ()) => return .skip
  | `(owl_tm| $b:str  ) => do
    return .bitstring b.getString
  | `(owl_tm| fix $f:owl_var ( $v:owl_var ) $e:owl_tm) => do
    let e' ← elabTm e P Rs D (elabVar f :: elabVar v :: G)
    return .fixlam (elabVar v) e'
  | `(owl_tm| Λ $v:owl_var . $e:owl_tm) => do
    let e' ← elabTm e P Rs (elabVar v :: D) G
    return .tlam e'
  | `(owl_tm| Λβ $v:owl_var . $e:owl_tm) => do
    let e' ← elabTm e (elabVar v :: P) Rs D G
    return .l_lam e'
  | `(owl_tm| Λr $id:ident . $e:owl_tm) => do
    let e' ← elabTm e P (id.getId.toString :: Rs) D G
    return .rlam e'
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .tm_pair e1 e2
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let tEx ← Term.elabTerm t (mkConst ``String)
    let tTy ← instantiateMVars (← inferType tEx)
    let s ← unsafe Meta.evalExpr String tTy tEx
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .binop s e1 e2
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm )) => do
    let tEx ← Term.elabTerm t (mkConst ``String)
    let tTy ← instantiateMVars (← inferType tEx)
    let s ← unsafe Meta.evalExpr String tTy tEx
    let e1 ← elabTm e1 P Rs D G
    return .unop s e1
-- | `(owl_tm| $ $t:term [ $ls:owl_label,* ] [ $ts:owl_type,* ] [ $es:owl_tm,* ]) => do
  --   let ls' <- ls.getElems.mapM elabLabel
  --   let ts' <- ts.getElems.mapM elabType
  --   let es' <- es.getElems.mapM elabTm
  --   let ls_list <- mkListLit (mkConst ``SLabel) ls'.toList
  --   let ts_list <- mkListLit (mkConst ``STy) ts'.toList
  --   let es_list <- mkListLit (mkConst ``SExpr) es'.toList
  --   let t' ← Term.elabTerm t (mkConst ``Owl.tm)
  --   mkAppM ``SExprX.embedtm #[t', ls_list, ts_list, es_list]
  | `(owl_tm| zero $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .zero e
  | `(owl_tm| $e1:owl_tm $e2:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .app e1 e2
  | `(owl_tm| alloc $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .alloc e
  | `(owl_tm| ! $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .dealloc e
  | `(owl_tm| $e1:owl_tm := $e2:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .assign e1 e2
  | `(owl_tm| π1 $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .left_tm e
  | `(owl_tm| π2 $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .right_tm e
  | `(owl_tm| ı1 $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .inl e
  | `(owl_tm| ı2 $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .inr e
  | `(owl_tm| case $e1:owl_tm with | inl $v1:owl_var => $e2:owl_tm | inr $v2:owl_var => $e3:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D (elabVar v1 :: G)
    let e3 ← elabTm e3 P Rs D (elabVar v2 :: G)
    return .case e1 e2 e3
  | `(owl_tm| $e:owl_tm [ $t:owl_type ]) => do
    let e ← elabTm e P Rs D G
    let t ← elabType t P Rs D
    return .tapp e t
  | `(owl_tm| $e:owl_tm [{$re:owl_rexp}]) => do
    let e ← elabTm e P Rs D G
    let re ← elab_rexp re P Rs
    return .rapp e re
  | `(owl_tm| $e:owl_tm ⟨ $l:owl_label ⟩) => do
    let e ← elabTm e P Rs D G
    let l ← elabLabel l P
    return .lapp e l
  | `(owl_tm| unpack $e1:owl_tm as ($v1:owl_var, $v2:owl_var) in $e2:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs (elabVar v1 :: D) (elabVar v2 :: G)
    return .unpack e1 e2
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let t ← elabType t P Rs D
    let e ← elabTm e P Rs D G
    return .pack t e
  | `(owl_tm| rpack ($re:owl_rexp, $e:owl_tm)) => do
    let re ← elab_rexp re P Rs
    let e ← elabTm e P Rs D G
    return .rpack re e
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    let e3 ← elabTm e3 P Rs D G
    return .if_tm e1 e2 e3
  | `(owl_tm| if corr($c:owl_label) then $e1:owl_tm else $e2:owl_tm) => do
    let c ← elabLabel c P
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .if_c c e1 e2
  | `(owl_tm| sync $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .sync e
  | `(owl_tm| union_elim $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let e ← elabTm e P Rs D G
    let b ← elabTm b P Rs D (id1.getId.toString :: G)
    return .union_elim e b
  | `(owl_tm| let $v1:owl_var = $e:owl_tm  in $b:owl_tm) => do
    let e ← elabTm e P Rs D G
    let b ← elabTm b P Rs D (elabVar v1 :: G)
    return .tlet e b
  | `(owl_tm| let $v1:owl_var : $t:owl_type = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = ($e : $t) in $b)) P Rs D G
  | `(owl_tm| let admit $v1:owl_var : $t:owl_type = $_:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = (admit : $t) in $b)) P Rs D G
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = π1 $e in let $v2 = π2 $e in $b)) P Rs D G
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var, $v3:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = π1 $e in let $v2 = π1 (π2 $e) in let $v3 = π2 (π2 $e) in $b)) P Rs D G
  | `(owl_tm| $e1:owl_tm ; $e2:owl_tm ) => do
    elabTmX (← `(owl_tm| (let _ = $e1 in $e2))) P Rs D G
  | `(owl_tm| λ ($v:owl_var : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    elabTmX (← `(owl_tm| ((λ $v => $e) : ($t1 -> $t2)))) P Rs D G
  | `(owl_tm| λ $v:owl_var => $e:owl_tm) => do
    let e ← elabTm e P Rs D ("_" :: elabVar v :: G)
    let unused := "unused variable"
    return .fixlam unused e
  | `(owl_tm| corr_case $l1:owl_label in $e:owl_tm ) => do
    let l ← elabLabel l1 P
    let e ← elabTm e P Rs D G
    return .corr_case l e
  | `(owl_tm| ( $e:owl_tm : $t:owl_type)) => do
    let e ← elabTm e P Rs D G
    let t ← elabType t P Rs D
    return .annot e t
  | _ => throwUnsupportedSyntax
end

/-

-- Phi Mappings
syntax "(" owl_phi_entry ")" : owl_phi_entry
syntax  ident owl_cond_sym owl_label : owl_phi_entry
syntax ident : owl_phi_entry

/-- One phi row: returns (new label-parameter name, condition × label). -/
partial def elabPhiOne (P : TCtx) : Syntax → TermElabM (String × (cond_sym × label (ScopeMap.ofList [P.length])))
  | `(owl_phi_entry| ( $e:owl_phi_entry)) => elabPhiOne P e
  | `(owl_phi_entry|  $id:ident $co:owl_cond_sym $lab:owl_label) => do
      let c ← elabCondSym co
      let l ← elabLabel lab P
      return (id.getId.toString, (c, l))
  | `(owl_phi_entry| $id:ident) => do
      let c : cond_sym := .geq
      let l : label (ScopeMap.ofList [P.length]) := .latl Owl.labelTmLattice.bot
      return (id.getId.toString, (c, l))
  | _ => throwUnsupportedSyntax

syntax "(" owl_delta_entry ")" : owl_delta_entry
syntax  ident "<:" owl_type : owl_delta_entry

partial def elabDeltaOne (P R D : TCtx) : Syntax → TermElabM (String × ty P.length R.length D.length 0)
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaOne P R D e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let t ← elabType t P R D []
      return (id.getId.toString, t)
  | _ => throwUnsupportedSyntax

syntax "(" owl_gamma_entry ")" : owl_gamma_entry
syntax  ident "=>" owl_type : owl_gamma_entry

partial def elabGammaOne (P R D : TCtx) : Syntax → TermElabM (String × ty P.length R.length D.length 0)
  | `(owl_gamma_entry| ( $e:owl_gamma_entry)) => elabGammaOne P R D e
  | `(owl_gamma_entry|  $id:ident => $t:owl_type) => do
      let t ← elabType t P R D []
      return (id.getId.toString, t)
  | _ => throwUnsupportedSyntax

syntax "(" owl_psi_entry ")" : owl_psi_entry
syntax  "corr(" owl_label ")" : owl_psi_entry
syntax  "¬corr(" owl_label ")" : owl_psi_entry

partial def elabPsiOne (P : TCtx) : Syntax → TermElabM (corruption P.length)
  | `(owl_psi_entry| ( $e:owl_psi_entry)) => elabPsiOne P e
  | `(owl_psi_entry| corr($l1:owl_label)) => do
      let l1 ← elabLabel l1 P
      return .corr l1
  | `(owl_psi_entry| ¬corr($l1:owl_label)) => do
      let l1 ← elabLabel l1 P
      return .not_corr l1
  | _ => throwUnsupportedSyntax

declare_syntax_cat owl_theta

syntax "·" : owl_theta
syntax owl_theta "," ident : owl_theta
syntax owl_theta "," owl_prop : owl_theta

syntax "(" owl_phi_entry "," owl_phi ")" : owl_phi
syntax owl_phi_entry "," owl_phi : owl_phi
syntax owl_phi_entry : owl_phi
syntax "(" owl_phi_entry ")" : owl_phi
syntax "·" : owl_phi

syntax "(" owl_delta_entry "," owl_delta ")" : owl_delta
syntax owl_delta_entry "," owl_delta : owl_delta
syntax owl_delta_entry : owl_delta
syntax "(" owl_delta_entry ")" : owl_delta
syntax "·" : owl_delta

syntax "(" owl_gamma_entry "," owl_gamma ")" : owl_gamma
syntax owl_gamma_entry "," owl_gamma : owl_gamma
syntax owl_gamma_entry : owl_gamma
syntax "(" owl_gamma_entry ")" : owl_gamma
syntax "·" : owl_gamma

syntax "(" owl_psi_entry "," owl_psi ")" : owl_psi
syntax owl_psi_entry "," owl_psi : owl_psi
syntax owl_psi_entry : owl_psi
syntax "(" owl_psi_entry ")" : owl_psi
syntax "·" : owl_psi

partial def phiSyntaxList (stx : Syntax) : TermElabM (List Syntax) :=
  match stx with
  | `(owl_phi| ($e1:owl_phi_entry, $rest:owl_phi)) => do
      let r ← phiSyntaxList rest
      return e1 :: r
  | `(owl_phi| $e1:owl_phi_entry , $rest:owl_phi) => do
      let r ← phiSyntaxList rest
      return e1 :: r
  | `(owl_phi| $e:owl_phi_entry) => return [e]
  | `(owl_phi| ($e:owl_phi_entry) ) => return [e]
  | `(owl_phi| · ) => return []
  | _ => throwUnsupportedSyntax

partial def elabPhiExpr (stx : Syntax) : TermElabM (Sigma (fun n => phi_context n)) := do
  let entries ← phiSyntaxList stx
  let rec go (es : List Syntax) (P : TCtx) (phi : phi_context P.length) : TermElabM (Sigma (fun n => phi_context n)) :=
    match es with
    | [] => return ⟨P.length, phi⟩
    | e :: es' => do
      let (nm, pr) ← elabPhiOne P e
      go es' (nm :: P) (pcons pr phi)
  go entries.reverse [] empty_phi

partial def deltaSyntaxList (stx : Syntax) : TermElabM (List Syntax) :=
  match stx with
  | `(owl_delta| ($e1:owl_delta_entry, $rest:owl_delta)) => do
      let r ← deltaSyntaxList rest
      return e1 :: r
  | `(owl_delta| $e1:owl_delta_entry , $rest:owl_delta) => do
      let r ← deltaSyntaxList rest
      return e1 :: r
  | `(owl_delta| $e:owl_delta_entry) => return [e]
  | `(owl_delta| ($e:owl_delta_entry) ) => return [e]
  | `(owl_delta| · ) => return []
  | _ => throwUnsupportedSyntax

partial def elabDeltaExpr (stx : Syntax) (P R : TCtx) : TermElabM (Sigma (fun n => delta_context P.length R.length n)) := do
  let entries ← deltaSyntaxList stx
  let rec go (es : List Syntax) (D : TCtx) (d : delta_context P.length R.length D.length) :
      TermElabM (Sigma (fun n => delta_context P.length R.length n)) :=
    match es with
    | [] => return ⟨D.length, d⟩
    | e :: es' => do
      let (nm, tyVal) ← elabDeltaOne P R D e
      go es' (nm :: D) (dcons tyVal d)
  go entries.reverse [] empty_delta

partial def gammaSyntaxList (stx : Syntax) : TermElabM (List Syntax) :=
  match stx with
  | `(owl_gamma| ($e1:owl_gamma_entry, $rest:owl_gamma)) => do
      let r ← gammaSyntaxList rest
      return e1 :: r
  | `(owl_gamma| $e1:owl_gamma_entry , $rest:owl_gamma) => do
      let r ← gammaSyntaxList rest
      return e1 :: r
  | `(owl_gamma| $e:owl_gamma_entry) => return [e]
  | `(owl_gamma| ($e:owl_gamma_entry) ) => return [e]
  | `(owl_gamma| · ) => return []
  | _ => throwUnsupportedSyntax

partial def elabGammaExpr (stx : Syntax) (P R D : TCtx) :
    TermElabM (Sigma (fun n => gamma_context P.length R.length D.length n)) := do
  let entries ← gammaSyntaxList stx
  let rec go (es : List Syntax) (G : TCtx) (g : gamma_context P.length R.length D.length G.length) :
      TermElabM (Sigma (fun n => gamma_context P.length R.length D.length n)) :=
    match es with
    | [] => return ⟨G.length, g⟩
    | e :: es' => do
      let (nm, tyVal) ← elabGammaOne P R D e
      go es' (nm :: G) (Owl.cons tyVal g)
  go entries.reverse [] empty_gamma

/-- Variable names for label parameters `P`, in the same order as `elabPhiExpr` / `elabPhi`. -/
partial def collectPhiVarNameOne (stx : Syntax) : TermElabM String :=
  match stx with
  | `(owl_phi_entry| ($e:owl_phi_entry)) => collectPhiVarNameOne e
  | `(owl_phi_entry| $id:ident $_:owl_cond_sym $_:owl_label) => return id.getId.toString
  | `(owl_phi_entry| $id:ident) => return id.getId.toString
  | _ => throwUnsupportedSyntax

partial def collectPhiVarNames (stx : Syntax) : TermElabM (List String) := do
  let entries ← phiSyntaxList stx
  let mut names : List String := []
  for e in entries.reverse do
    names := (← collectPhiVarNameOne e) :: names
  return names

partial def collectDeltaVarNameOne (stx : Syntax) : TermElabM String :=
  match stx with
  | `(owl_delta_entry| ($e:owl_delta_entry)) => collectDeltaVarNameOne e
  | `(owl_delta_entry| $id:ident <: $_:owl_type) => return id.getId.toString
  | _ => throwUnsupportedSyntax

partial def collectDeltaVarNames (stx : Syntax) : TermElabM (List String) := do
  let entries ← deltaSyntaxList stx
  let mut names : List String := []
  for e in entries.reverse do
    names := (← collectDeltaVarNameOne e) :: names
  return names

partial def collectGammaVarNameOne (stx : Syntax) : TermElabM String :=
  match stx with
  | `(owl_gamma_entry| ($e:owl_gamma_entry)) => collectGammaVarNameOne e
  | `(owl_gamma_entry| $id:ident => $_:owl_type) => return id.getId.toString
  | _ => throwUnsupportedSyntax

partial def collectGammaVarNames (stx : Syntax) : TermElabM (List String) := do
  let entries ← gammaSyntaxList stx
  let mut names : List String := []
  for e in entries.reverse do
    names := (← collectGammaVarNameOne e) :: names
  return names

/-- Refinement-parameter names bound in `owl_theta`, outermost last (matches old `STheta.getVars`). -/
partial def collectThetaVarNames (stx : Syntax) : List String :=
  match stx with
  | `(owl_theta| ·) => []
  | `(owl_theta| $th:owl_theta, $id:ident) => id.getId.toString :: collectThetaVarNames th
  | `(owl_theta| $th:owl_theta, $_:owl_prop) => collectThetaVarNames th
  | _ => []

partial def psiSyntaxList (stx : Syntax) : TermElabM (List Syntax) :=
  match stx with
  | `(owl_psi| ($e1:owl_psi_entry, $rest:owl_psi)) => do
      let r ← psiSyntaxList rest
      return e1 :: r
  | `(owl_psi| $e1:owl_psi_entry , $rest:owl_psi) => do
      let r ← psiSyntaxList rest
      return e1 :: r
  | `(owl_psi| $e:owl_psi_entry) => return [e]
  | `(owl_psi| ($e:owl_psi_entry) ) => return [e]
  | `(owl_psi| · ) => return []
  | _ => throwUnsupportedSyntax

partial def elabPsiExpr (stx : Syntax) (P : TCtx) : TermElabM (psi_context P.length) := do
  let entries ← psiSyntaxList stx
  entries.mapM (elabPsiOne P)

partial def elabThetaExpr (stx : Syntax) (R : TCtx) : TermElabM (RCtx R.length) :=
  match stx with
  | `(owl_theta| ·) => return []
  | `(owl_theta| $th:owl_theta, $_:ident) =>
    elabThetaExpr th R
  | `(owl_theta| $th:owl_theta, $p:owl_prop) => do
    let tail ← elabThetaExpr th R
    let pe ← elab_prop p R []
    return pe :: tail
  | _ => throwUnsupportedSyntax

partial def elabPhi (stx : Syntax) : TermElabM (Sigma (fun n => phi_context n)) :=
  elabPhiExpr stx

/-- Like `elabPhi` but requires the built context to have exactly `expected` label parameters. -/
def elabPhiLen (stx : Syntax) (expected : Nat) : TermElabM (phi_context expected) := do
  let ⟨n, phi⟩ ← elabPhiExpr stx
  if h : n = expected then return h ▸ phi
  else throwError s!"phi length mismatch: got {n}, expected {expected}"

partial def elabDelta (stx : Syntax) (P R : TCtx := []) :
    TermElabM (Sigma (fun n => delta_context P.length R.length n)) :=
  elabDeltaExpr stx P R

def elabDeltaLen (stx : Syntax) (P R : TCtx) (expected : Nat) :
    TermElabM (delta_context P.length R.length expected) := do
  let ⟨n, d⟩ ← elabDeltaExpr stx P R
  if h : n = expected then return h ▸ d
  else throwError s!"delta length mismatch: got {n}, expected {expected}"

partial def elabGamma (stx : Syntax) (P R D : TCtx := []) :
    TermElabM (Sigma (fun n => gamma_context P.length R.length D.length n)) :=
  elabGammaExpr stx P R D

def elabGammaLen (stx : Syntax) (P R D : TCtx) (expected : Nat) :
    TermElabM (gamma_context P.length R.length D.length expected) := do
  let ⟨n, g⟩ ← elabGammaExpr stx P R D
  if h : n = expected then return h ▸ g
  else throwError s!"gamma length mismatch: got {n}, expected {expected}"

partial def elabPsi (stx : Syntax) (P : TCtx := []) : TermElabM (psi_context P.length) :=
  elabPsiExpr stx P

/-- Elaborate `owl_theta` into `List (prop R.length 0)` (alias for `elabThetaExpr`). -/
def elabTheta (stx : Syntax) (R : TCtx := []) : TermElabM (RCtx R.length) :=
  elabThetaExpr stx R

-- test parser for labels
elab "phi_parse" "(" p:owl_phi ")" : term => do
  let lvars ← collectPhiVarNames p
  let phi ← elabPhiLen p lvars.length
  mkAppM ``vec.to_fn #[toExpr (vec.from_fn phi)]

-/

/-
---- Declarations

syntax "type" ident "=" owl_type  : owl_decl_entry
syntax "let" ident "=" owl_tm : owl_decl_entry
syntax owl_decl_entry* : owl_decl

structure ParserScope where
  P : TCtx
  R : TCtx
  D : TCtx
  G : TCtx

def ParserScope.toScopeEnv (se : ParserScope) : ScopeEnv :=
  { l := se.P.length, r := se.R.length, d := se.D.length, m := se.G.length }

partial def elabDeclEntry (stx : Syntax) (se : ParserScope) : TermElabM ((se' : ParserScope) × (Decl se.toScopeEnv se'.toScopeEnv)) :=
  match stx with
  | `(owl_decl_entry| type $id:ident = $t:owl_type) => do
    let t ← elabType t se.P se.R se.D se.G
    return ⟨{se with D := id.getId.toString :: se.D}, .DeclTy id.getId.toString t⟩
  | `(owl_decl_entry| let $id:ident = $e:owl_tm) => do
    let e ← elabTm e se.P se.R se.D se.G
    return ⟨{se with G := id.getId.toString :: se.G}, .DeclTm id.getId.toString e⟩
  | _ => throwUnsupportedSyntax

partial def elabDecl (stx : Syntax) (se : ParserScope) : TermElabM ((se' : ParserScope) × (Decl se.toScopeEnv se'.toScopeEnv)) :=
 match stx with
 | `(owl_decl| $es:owl_decl_entry*) =>
  let es' := es.toList
  es'.foldlM (fun acc d => do
    let ⟨se', d'⟩ := acc
    let ⟨se'', d''⟩ ← elabDeclEntry d.raw se'
    return ⟨se'', .DeclApp d' d''⟩
  ) ⟨se, .Nil⟩
 | _ => throwUnsupportedSyntax

-/
