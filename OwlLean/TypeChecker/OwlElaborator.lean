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
declare_syntax_cat owl_tm_field_entry
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_type_field_entry
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
declare_syntax_cat owl_decl_entry (behavior := both)
declare_syntax_cat owl_decl (behavior := both)

private def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => none

private def getScopeMapFromTy (ty : Expr) : MetaM (ScopeMap 3) := do
  let ty ← whnf ty
  unless ty.getAppFn.isConstOf ``Owl.ty do
    throwError s!"expected Owl.ty …, got {ty}"
  let a := ty.getAppArgs
  unless 1 ≤ a.size do throwError s!"ty application too small: {ty} got {a.size} argu"
  let s := a[0]!
  unsafe evalExpr (ScopeMap 3) (mkApp (mkConst ``ScopeMap) (mkNatLit 3)) s

private def getScopeMapFromTm (ty : Expr) : MetaM (ScopeMap 4) := do
  let ty ← whnf ty
  unless ty.getAppFn.isConstOf ``Owl.tm do
    throwError s!"expected Owl.tm …, got {ty}"
  let a := ty.getAppArgs
  unless 1 ≤ a.size do throwError s!"tm application too small: {ty} got {a.size} argu"
  let s := a[0]!
  unsafe evalExpr (ScopeMap 4) (mkApp (mkConst ``ScopeMap) (mkNatLit 4)) s

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

def subst_tm (T : tm (ScopeMap.ofList [l, r, t, e]))
  (f : Fin l -> label (ScopeMap.ofList [l']))
  (g : Fin r -> rexp (ScopeMap.ofList [l', r']))
  (h : Fin t -> ty (ScopeMap.ofList [l', r', t']))
  (k : Fin e -> tm (ScopeMap.ofList [l', r', t', e'])) :
  tmX (ScopeMap.ofList [l', r', t', e']) :=
  T.get.subst $ ⟨fun j i =>
    match j with
    | 0 => f i
    | 1 => g i
    | 2 => h i
    | 3 => (k i).get
    ⟩

partial def elabLabel (stx : Syntax) (P : TCtx) : TermElabM (label (ScopeMap.ofList [P.length])) :=
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
      | .none => do
        logErrorAt id s!"Unknown label variable: {nm}"
        throwError s!"Error while checking label"
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
      else do
        logErrorAt l s!"embedlabel: length mismatch: expected {lLen}, got {xsList.length}"
        throwError s!"Error while checking label"
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
      else do
        logErrorAt l s!"embedlabel: empty arg list but embedded label is not arity 0"
        throwError s!"Error while checking label"
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

partial def elabConstr (stx : Syntax) (P : TCtx) : TermElabM (constr (ScopeMap.ofList [P.length])) :=
  match stx with
  | `(owl_constr| ( $e:owl_constr)) => elabConstr e P
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let l1 ← elabLabel l1 P
      let l2 ← elabLabel l2 P
      let c ← elabCondSym c
      return .condition c l1 l2
  | _ => throwUnsupportedSyntax


syntax ident : owl_rexp
syntax "⟦" ident "⟧" "(" owl_rexp,* ")" : owl_rexp
syntax str : owl_rexp


partial def elab_rexp (stx : Syntax) (P : TCtx) (Rs : TCtx) : TermElabM (rexp (ScopeMap.ofList [P.length, Rs.length])) :=
  match stx with
  | `(owl_rexp | ⟦ $op:ident ⟧ ( $es:owl_rexp,* )) => do
    let esVals ← es.getElems.mapM (elab_rexp · P Rs)
    let esList := esVals.toList
    return .op op.getId.toString (rexp_list.mk esList)
  | `(owl_rexp | $i:ident ) => do
    let nm := i.getId.toString
    match Rs.lookup nm with
    | .none => do
      logErrorAt i s!"Unknown refinement variable: {nm}"
      throwError s!"Error while checking refinement"
    | .some j => return .var j
  | `(owl_rexp |  $ob:str  ) => do
    return .const ob.getString.toList
  | _ => throwUnsupportedSyntax


declare_syntax_cat owl_prop (behavior := both)
syntax "(" owl_prop ")" : owl_prop
syntax owl_rexp "=" owl_rexp : owl_prop
syntax owl_prop "∧" owl_prop : owl_prop
syntax owl_prop "∨" owl_prop : owl_prop
syntax owl_prop "=>" owl_prop : owl_prop
syntax "¬" owl_prop : owl_prop
syntax "∀" ident "." owl_prop : owl_prop
syntax &"True" : owl_prop
syntax &"False" : owl_prop

partial def elab_prop (stx : Syntax) (P : TCtx) (Rs : TCtx)  : TermElabM (prop (ScopeMap.ofList [P.length, Rs.length])) :=
  match stx with
  | `(owl_prop| ( $e:owl_prop )) => elab_prop e P Rs
  | `(owl_prop | True ) => return .ptrue
  | `(owl_prop | False ) => return (.pnot .ptrue)
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
  | `(owl_prop| $p1:owl_prop => $p2:owl_prop) => do
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
syntax "if" "corr" owl_label "then" owl_type "else" owl_type : owl_type
syntax "Public" : owl_type
syntax "$" term:max "[" owl_label,* "]" "[" owl_rexp,* "]" "[" owl_type,* "]" : owl_type
syntax owl_type "{" owl_prop "}" : owl_type
syntax ident ":" owl_type : owl_type_field_entry
syntax "{" owl_type_field_entry,* "}" : owl_type

partial def elabType (stx : Syntax) (P : TCtx) (Rs : TCtx) (D : TCtx) :
    TermElabM (ty (ScopeMap.ofList [P.length, Rs.length, D.length])) := do
  let stx <- liftMacroM <| expandMacros stx
  match stx with
  | `(owl_type| ( $e:owl_type)) => elabType e P Rs D
  | `(owl_type| $id:ident) => do
      let nm := id.getId.toString
      match D.lookup nm with
      | .none => do
        logErrorAt id s!"Unknown type variable: {nm}"
        throwError s!"Error while checking type"
      | .some j => return .var_ty id.getId.toString j
  | `(owl_type| Any) => return .Any
  | `(owl_type| unit) => return .Unit
  | `(owl_type| Public) => return .Public
  | `(owl_type| { $es:owl_type_field_entry,* }) => do
    let es' <- es.getElems.toList.mapM fun e =>
      match e.raw with
      | `(owl_type_field_entry | $n:ident : $t:owl_type) => do
        let t ← elabType t P Rs D
        return (n.getId.toString, t)
      | _ => throwUnsupportedSyntax
    unless es' |>.map (·.1) |>.uniq? do
      logErrorAt stx s!"Record fields must be unique"
      throwError s!"Error while checking record type"
    unless es'.length > 1 do
      logErrorAt stx s!"Record must have at least one field"
      throwError s!"Error while checking record type"
    let es' := es'.sort_assocs
    return .record (ty_record.mk es')
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
  | `(owl_type| if corr $c:owl_label then $t1:owl_type else $t2:owl_type) => do
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
    let tEx ← Term.elabTerm t none
    let tTy ← instantiateMVars (← inferType tEx)
    let ty_s <- getScopeMapFromTy tTy
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
/-
Precedences mirror core `term` application (`syntax:lead … :lead … :arg` for juxtaposition):
atoms must resolve to `:max`; otherwise they keep metavariable precedence `0` and cannot appear
left of juxtaposition (`f x` fails).

Binder and `let` bodies use `owl_tm:min` (not `:lead`): sequence (`;`) is only `syntax:min`, so its
syntax node cannot sit under a slot that requires `:lead`; `owl_tm:min` accepts juxtaposition too
because `lead > min`.

Inside parentheses parse `owl_tm:min` so application spines `(f g h)` and sequences `(a ; b)` both work.

Sequences use `:min / :min1` operands so `a ; b ; c` parses left-associated (like notation `LXOR`);
`syntax:1` produced a node weaker than binder bodies could consume.
-/
syntax:max "(" owl_tm:min ")" : owl_tm
syntax:max ident : owl_tm
syntax:max num : owl_tm
syntax:max "error" : owl_tm
syntax:max "()" : owl_tm
syntax:max str : owl_tm
syntax:max "fix" owl_var "(" owl_var ")" owl_tm:min : owl_tm
syntax:max "Λ" owl_var "." owl_tm:min : owl_tm
syntax:max "Λβ" owl_var "." owl_tm:min : owl_tm
syntax:max "Λr" ident "." owl_tm:min : owl_tm
syntax:max "⟨" owl_tm:lead "," owl_tm:lead "⟩" : owl_tm
syntax:max "⟦" ident "⟧" "(" owl_tm:lead,* ")" : owl_tm
syntax:max "zero" owl_tm:arg : owl_tm
syntax:lead owl_tm:lead owl_tm:arg : owl_tm
syntax:max "alloc" owl_tm:arg : owl_tm
syntax:max "!" owl_tm:arg : owl_tm
syntax:lead owl_tm:lead ":=" owl_tm:min : owl_tm
syntax:max "π1" owl_tm:arg : owl_tm
syntax:max "π2" owl_tm:arg : owl_tm
syntax:max "ı1" owl_tm:arg : owl_tm
syntax:max "ı2" owl_tm:arg : owl_tm
syntax:lead "case" owl_tm:lead "with" "|" "inl" owl_var "=>" owl_tm:min "|" "inr" owl_var "=>" owl_tm:min : owl_tm
syntax:lead owl_tm:lead "[" owl_type "]" : owl_tm
syntax:lead owl_tm:lead "[{" owl_rexp "}]" : owl_tm
syntax:lead owl_tm:lead "⟨" owl_label "⟩" : owl_tm
syntax:max "pack" "(" owl_type "," owl_tm:min ")" : owl_tm
syntax:max "rpack" "(" owl_rexp "," owl_tm:min ")" : owl_tm
syntax:max "unpack" owl_tm:lead "as" "(" owl_var "," owl_var ")" "in" owl_tm:min : owl_tm
syntax:lead "if" owl_tm:lead "then" owl_tm:min "else" owl_tm:min : owl_tm
syntax:max "if" "corr" "(" owl_label ")" "then" owl_tm:min "else" owl_tm:min : owl_tm
syntax:max "get_val" ident " = " owl_tm:lead " in " owl_tm:min : owl_tm
syntax:max "secparam" : owl_tm
syntax:max "sample" owl_tm:arg : owl_tm
syntax:max "union_elim" ident "=" owl_tm:lead "in" owl_tm:min : owl_tm
syntax:max "let" owl_var "=" owl_tm:min "in" owl_tm:min : owl_tm
syntax:min owl_tm:min ";" owl_tm:min1 : owl_tm
syntax:max "let" owl_var ":" owl_type "=" owl_tm:min "in" owl_tm:min : owl_tm
syntax:max "let" "admit" owl_var ":" owl_type "=" owl_tm:min "in" owl_tm:min : owl_tm
syntax:max "let" "(" owl_var "," owl_var ")" "=" owl_tm:min "in" owl_tm:min : owl_tm
syntax:max "let" "(" owl_var "," owl_var "," owl_var ")" "=" owl_tm:min "in" owl_tm:min : owl_tm
syntax:max "λ" "(" owl_var ":" owl_type ")" ":" owl_type "=>" owl_tm:min : owl_tm
syntax:max "λ" owl_var "=>" owl_tm:min : owl_tm
syntax "$" term:max "[" owl_label,* "]" "[" owl_rexp,* "]" "[" owl_type,* "]" "[" owl_tm:min,* "]" : owl_tm
syntax:max "corr_case" owl_label "in" owl_tm:min : owl_tm
syntax:max "(" owl_tm:min ":" owl_type ")" : owl_tm
syntax:lead owl_tm:lead "." num : owl_tm
syntax:max "assert" "(" owl_prop ")" : owl_tm
syntax:max "admit" : owl_tm
syntax ident ":=" owl_tm : owl_tm_field_entry
syntax:max "{" owl_tm_field_entry,* "}" : owl_tm
syntax:max owl_tm "^." ident : owl_tm
syntax "type" ident "=" owl_type "in" owl_tm : owl_tm

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

def Owl.tm_list.mk (ls : List (String × tm s)) : tm_list s :=
  match ls with
  | [] => .nil
  | (s, e) :: ls => .cons s e (tm_list.mk ls)

mutual
  partial def elabTm (stx : Syntax) (P Rs D G : TCtx) : TermElabM (tm (ScopeMap.ofList [P.length, Rs.length, D.length, G.length])) := do
    let stx <- liftMacroM <| expandMacros stx
    let body ← elabTmX stx P Rs D G
    return .mk (mkOpaqueSyntax stx) body

  partial def elabTmX (stx : Syntax) (P Rs D G : TCtx) : TermElabM (tmX (ScopeMap.ofList [P.length, Rs.length, D.length, G.length])) :=
  match stx with
  | `(owl_tm| ( $e:owl_tm)) => elabTmX e P Rs D G
  | `(owl_tm| admit ) => return .admit
  | `(owl_tm| $e:owl_tm ^. $n:ident) => do
    let e ← elabTm e P Rs D G
    return .get_record n.getId.toString e
  | `(owl_tm| { $es:owl_tm_field_entry,* }) => do
       let es' <- es.getElems.toList.mapM fun e =>
          match e.raw with
          | `(owl_tm_field_entry | $n:ident := $e:owl_tm) => do
            let e ← elabTm e P Rs D G
            return (n.getId.toString, e)
          | _ => throwUnsupportedSyntax
       return .mk_record (Owl.tm_list.mk es')
  | `(owl_tm | $n:num ) =>
    return .bitstring (Nat.toDigits 10 n.getNat)
  | `(owl_tm| $id:ident) => do
      let nm := id.getId.toString
      match G.lookup nm with
      | .none => do
        logErrorAt id s!"Unknown term variable: {nm}"
        throwError s!"Error while checking term"
      | .some j => return .var_tm j
  | `(owl_tm| ()) => return .unit
  | `(owl_tm| $b:str  ) => do
    return .bitstring b.getString.toList
  | `(owl_tm| type $id:ident = $t:owl_type in $e:owl_tm) => do
    let t ← elabType t P Rs D
    let e ← elabTm e P Rs (id.getId.toString :: D) G
    let sub : ScopeMap.Subst 4 TmFunctors
                          (ScopeMap.ofList [P.length, Rs.length, (id.getId.toString :: D).length, G.length])
                          (ScopeMap.ofList [P.length, Rs.length, D.length, G.length]) :=
        (@ScopeMap.Subst.down 4 #Ty TmFunctors (ScopeMap.ofList [P.length, Rs.length, D.length, G.length]) t)
    return (e.subst $ sub).get
  | `(owl_tm| fix $f:owl_var ( $v:owl_var ) $e:owl_tm) => do
    let e' ← elabTm e P Rs D (elabVar f :: elabVar v :: G)
    return .fixlam (elabVar f) (elabVar v) e'
  | `(owl_tm| Λ $v:owl_var . $e:owl_tm) => do
    let e' ← elabTm e P Rs (elabVar v :: D) G
    return .tlam (elabVar v) e'
  | `(owl_tm| Λβ $v:owl_var . $e:owl_tm) => do
    let e' ← elabTm e (elabVar v :: P) Rs D G
    return .l_lam (elabVar v) e'
  | `(owl_tm| Λr $id:ident . $e:owl_tm) => do
    let e' ← elabTm e P (id.getId.toString :: Rs) D G
    return .rlam (id.getId.toString) e'
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs D G
    return .tm_pair e1 e2
  | `(owl_tm| ⟦ $t:ident ⟧ ( $es:owl_tm,* )) => do
    let esVals <- es.getElems.mapM (elabTm · P Rs D G)
    let esList := esVals.toList.map (fun e => ("", e))
    return .op t.getId.toString (tm_list.mk esList)
  | `(owl_tm| $ $t:term [ $ls:owl_label,* ] [ $rs:owl_rexp,* ] [ $ts:owl_type,* ] [ $es:owl_tm,* ]) => do
      let lsVals <- Array.toList <$> ls.getElems.mapM (elabLabel · P)
      let rsVals <- Array.toList <$> rs.getElems.mapM (elab_rexp · P Rs)
      let tsVals <- Array.toList <$> ts.getElems.mapM (elabType · P Rs D)
      let esVals <- Array.toList <$> es.getElems.mapM (elabTm · P Rs D G)
      let tEx ← Term.elabTerm t none
      let tTy <- instantiateMVars (← inferType tEx)
      let tScope <- getScopeMapFromTm tTy
      if tScope = ScopeMap.ofList [lsVals.length, rsVals.length, tsVals.length, esVals.length] then
        let tVal ← liftM <| unsafe Meta.evalExpr (α := tm (ScopeMap.ofList [lsVals.length, rsVals.length, tsVals.length, esVals.length])) tTy tEx
        return subst_tm tVal (lsVals.get) (rsVals.get) (tsVals.get) (esVals.get)
      else throwError s!"embedtm"
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
    return .case e1 (elabVar v1) e2 (elabVar v2) e3
  | `(owl_tm| $e:owl_tm [ $t:owl_type ]) => do
    let e ← elabTm e P Rs D G
    let t ← elabType t P Rs D
    return .tapp e t
  | `(owl_tm| $e:owl_tm [{$re:owl_rexp}]) => do
    let e ← elabTm e P Rs D G
    let re ← elab_rexp re P Rs
    return .rapp e re
  | `(owl_tm| get_val $rname:ident = $e:owl_tm in $t:owl_tm) => do
    let e ← elabTm e P Rs D G
    let t ← elabTm t P (rname.getId.toString :: Rs) D G
    return .get_val rname.getId.toString e t
  | `(owl_tm| $e:owl_tm ⟨ $l:owl_label ⟩) => do
    let e ← elabTm e P Rs D G
    let l ← elabLabel l P
    return .lapp e l
  | `(owl_tm| unpack $e1:owl_tm as ($v1:owl_var, $v2:owl_var) in $e2:owl_tm) => do
    let e1 ← elabTm e1 P Rs D G
    let e2 ← elabTm e2 P Rs (elabVar v1 :: D) (elabVar v2 :: G)
    return .unpack e1 (elabVar v1) (elabVar v2) e2
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let t ← elabType t P Rs D
    let e ← elabTm e P Rs D G
    return .pack t e
  | `(owl_tm| assert ($p:owl_prop)) => do
    elabTmX (← `(owl_tm| ( () : unit { $p } ) )) P Rs D G
  | `(owl_tm| rpack ($re:owl_rexp, $e:owl_tm)) => do
    let re ← elab_rexp re P Rs
    let e ← elabTm e P Rs D G
    return .rpack re e
  | `(owl_tm| secparam) => return .secparam
  | `(owl_tm| sample $e:owl_tm) => do
    let e ← elabTm e P Rs D G
    return .sample e
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
  | `(owl_tm| union_elim $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let e ← elabTm e P Rs D G
    let b ← elabTm b P Rs D (id1.getId.toString :: G)
    return .union_elim (id1.getId.toString) e b
  | `(owl_tm| $e1:owl_tm ; $e2:owl_tm ) => do
     elabTmX (← `(owl_tm| (let _ = $e1 in $e2))) P Rs D G
  | `(owl_tm| let $v1:owl_var = $e:owl_tm  in $b:owl_tm) => do
    let e ← elabTm e P Rs D G
    let b ← elabTm b P Rs D (elabVar v1 :: G)
    return .tlet (elabVar v1) e b
  | `(owl_tm| let $v1:owl_var : $t:owl_type = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = ($e : $t) in $b)) P Rs D G
  | `(owl_tm| let admit $v1:owl_var : $t:owl_type = $_:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = (admit : $t) in $b)) P Rs D G
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = π1 $e in let $v2 = π2 $e in $b)) P Rs D G
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var, $v3:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (← `(owl_tm| let $v1 = π1 $e in let $v2 = π1 (π2 $e) in let $v3 = π2 (π2 $e) in $b)) P Rs D G
  | `(owl_tm| λ ($v:owl_var : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    elabTmX (← `(owl_tm| ((λ $v => $e) : ($t1 -> $t2)))) P Rs D G
  | `(owl_tm| λ $v:owl_var => $e:owl_tm) => do
    let e ← elabTm e P Rs D ("_" :: elabVar v :: G)
    let unused := "unused variable"
    return .fixlam unused (elabVar v) e
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

---- Declarations

syntax &"type" ident "<:" owl_type  : owl_decl_entry
syntax &"def" ident ":=" owl_tm : owl_decl_entry
syntax &"def" ident ":" owl_type ":=" owl_tm : owl_decl_entry
syntax &"assume" ident ":" owl_type : owl_decl_entry
syntax &"label" ident owl_cond_sym owl_label : owl_decl_entry
syntax owl_decl_entry* : owl_decl


structure ParserScope where
  P : TCtx
  R : TCtx
  D : TCtx
  G : TCtx

def ParserScope.toScopeMap (se : ParserScope) : ScopeMap 4 :=
  ScopeMap.ofList [se.P.length, se.R.length, se.D.length, se.G.length]

def elabDeclEntry (stx : Syntax) (se : ParserScope) : TermElabM ((se' : ParserScope) × (Decl se.toScopeMap se'.toScopeMap)) :=
  match stx with
  | `(owl_decl_entry| type $id:ident <: $t:owl_type) => do
    let t ← elabType t se.P se.R se.D
    return ⟨{se with D := id.getId.toString :: se.D}, .DeclTy (id.getId) t⟩
  | `(owl_decl_entry| def $id:ident := $e:owl_tm) => do
    let e ← elabTm e se.P se.R se.D se.G
    return ⟨{se with G := id.getId.toString :: se.G}, .DeclTm (id.getId) e none⟩
  | `(owl_decl_entry| def $id:ident : $t:owl_type := $e:owl_tm) => do
    let e ← elabTm e se.P se.R se.D se.G
    let t ← elabType t se.P se.R se.D
    return ⟨{se with G := id.getId.toString :: se.G}, .DeclTm (id.getId) e (some t)⟩
  | `(owl_decl_entry| assume $id:ident : $t:owl_type) => do
    let t ← elabType t se.P se.R se.D
    return ⟨{se with G := id.getId.toString :: se.G}, .DeclTmAssume (id.getId) t⟩
  | `(owl_decl_entry| label $id:ident $cs:owl_cond_sym $l:owl_label) => do
    let l ← elabLabel l se.P
    let cs ← elabCondSym cs
    return ⟨{se with P := id.getId.toString :: se.P}, .DeclLabel (id.getId) cs l⟩
  | _ => throwUnsupportedSyntax

def elabDeclsFrom (stx : Syntax) (se : ParserScope) : TermElabM ((se' : ParserScope) × (Decl se.toScopeMap se'.toScopeMap)) :=
  match stx with
  | `(owl_decl| $es:owl_decl_entry*) =>
    let es' := es.toList
    es'.foldlM (fun acc d => do
      let ⟨se', d'⟩ := acc
      let ⟨se'', d''⟩ ← elabDeclEntry d.raw se'
      return ⟨se'', .DeclApp d' d''⟩
    ) ⟨se, .Nil⟩
  | _ => throwUnsupportedSyntax

def elabDecls stx := elabDeclsFrom stx {P := [], R := [], D := [], G := []}
