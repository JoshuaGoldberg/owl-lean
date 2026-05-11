import OwlLean.TypeChecker.OwlElaborator
import OwlLean.TypeChecker.OwlTyping
import Lean
import Std.Data.HashMap

open Owl
open Lean Elab Meta

/-

elab "label_parse" "(" p:owl_label ")" : term => do
  return toExpr (← elabLabel p)

elab "cond_sym_parse" "(" p:owl_cond_sym ")" : term => do
  return toExpr (← elabCondSym p)

elab "constraint_parse" "(" p:owl_constr ")" : term => do
  return toExpr (← elabConstr p)

elab "type_parse" "(" p:owl_type ")" : term => do
  return toExpr (← elabType p)

elab "term_parse" "(" p:owl_tm ")" : term => do
  return toExpr (← elabTm p)

elab "Owl_Parse" "{" p:owl_tm "}" : term => do
  return toExpr (← elabTm p)

@[simp]
def PhiEntails (phi : phi_context n) (cond : constr n) : Prop :=
  phi |= cond

elab "(" phi:owl_phi " ⊨ " cond:owl_constr ")" : term => do
  let lvars ← collectPhiVarNames phi
  let phiV ← elabPhiLen phi lvars.length
  let phiE ← mkAppM ``vec.to_fn #[toExpr (vec.from_fn phiV)]
  let condE := toExpr (← elabConstr cond lvars)
  mkAppM ``PhiEntails #[phiE, condE]

elab "Ψ:=" p:owl_phi : term => do
  let lvars ← collectPhiVarNames p
  let phiV ← elabPhiLen p lvars.length
  mkAppM ``vec.to_fn #[toExpr (vec.from_fn phiV)]

-/


elab "Owl" "[" lvars:ident,* "]" "[" rvars:ident,* "]" "[" tvars:ident,* "]" "[" vars:ident,* "]" "{" p:owl_tm "}" : term => do
  let varNames := vars.getElems.map (fun id => id.getId.toString)
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let rvarNames := rvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let varList := varNames.toList
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList
  let rvarList := rvarNames.toList
  return toExpr (← elabTm p lvarList rvarList tvarList varList)

/--
`OwlTy_with [ls] [rs] [tvs] { τ }` elaborates `τ` under the given label, refinement, and type-variable contexts.
-/
elab "OwlTy_with" "[" lvars:ident,* "]" "[" rvars:ident,* "]" "[" tvars:ident,* "]" "{" p:owl_type "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let rvarNames := rvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList
  let rvarList := rvarNames.toList
  let τ ← elabType p lvarList rvarList tvarList
  Term.synthesizeSyntheticMVarsNoPostponing
  return toExpr τ

elab "OwlTy" "{" p:owl_type "}" : term => do
  Term.elabTerm (← `(OwlTy_with [] [] [] { $p })) .none

elab "OwlLabel" "[" lvars:ident,* "]" "{" p:owl_label "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let lvarList := lvarNames.toList
  return toExpr (← elabLabel p lvarList)

structure Sequent where
  l : Nat
  r : Nat
  d : Nat
  m : Nat
  Phi : lbl_ctx (ScopeMap.ofList [l])
  Psi : corr_ctx (ScopeMap.ofList [l])
  Delta : ty_var_ctx (ScopeMap.ofList [l, r, d])
  Theta : prop_ctx (ScopeMap.ofList [l, r])
  Gamma : tm_ctx (ScopeMap.ofList [l, r, d, m])
  e : tm (ScopeMap.ofList [l, r, d, m])
  t : ty (ScopeMap.ofList [l, r, d])

opaque owl_f_interp' : String -> String -> String -> String

def owl_f_interp (s x y : String) : String :=
  match s with
  | "concat" => x ++ y
  | _ => owl_f_interp' s x y

def doTc (n : TSyntax `ident) (s : Sequent) := do
  let env : Env (ScopeMap.ofList [s.l, s.r, s.d, s.m]) := {
    defName := n.getId,
    lbl := s.Phi
    corrs := s.Psi,
    ty_vars := s.Delta,
    hyps := s.Theta,
    tms := s.Gamma
    curSyntax := none }

  match ← ReaderT.run (infer s.e (some s.t)) env with
  | .ok _ => do
    println! "Successfully checked {n}"
  | .err e =>
    logError s!"err: {e.2}"
    match e.1 with
    | .none => PURE
    | .some v =>
      logErrorAt v.inner e.2

/-
syntax "#tc_with" ident ":=" owl_phi ";" owl_psi ";" owl_delta ";" owl_theta ";" owl_gamma "⊢" owl_tm ":" owl_type : command
elab_rules : command
  | `(#tc_with $n := $p ; $ps; $d; $th; $g ⊢ $e : $t ) => do
    let seq ← Command.liftTermElabM $ withEnableInfoTree false do
      let lvars ← collectPhiVarNames p
      let rvars := collectThetaVarNames th
      let tvars ← collectDeltaVarNames d
      let vars ← collectGammaVarNames g
      let phi ← elabPhiLen p lvars.length
      let psi ← elabPsi ps lvars
      let delta ← elabDeltaLen d lvars rvars tvars.length
      let gamma ← elabGammaLen g lvars rvars tvars vars.length
      let theta ← elabTheta th rvars
      let tmE ← elabTm e lvars rvars tvars vars
      let tyE ← elabType t lvars rvars tvars []
      return Sequent.mk lvars.length rvars.length tvars.length vars.length
        phi psi delta theta gamma tmE tyE
    Command.liftTermElabM $ doTc n seq
-/

elab "#tc" n:ident ":=" "⊢" "{" e:owl_tm "}" ":" t:owl_type : command => do
  let seq ← Command.liftTermElabM $ withEnableInfoTree false do
    let tmE ← elabTm e [] [] [] []
    let tyE ← elabType t [] [] []
    return Sequent.mk 0 0 0 0 .nil [] .nil [] .nil tmE tyE
  Command.liftTermElabM $ doTc n seq
--    Command.elabCommand (← `(#tc_with $n := · ; · ; · ; · ; ·  ⊢ $e : $t))


-- Example (must live in a downstream module so `command_elab` from `elab` above is active):
-- #tc foo := ⊢ { 32 } : Public
