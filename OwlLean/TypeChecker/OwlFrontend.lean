import OwlLean.TypeChecker.OwlElaborator
import OwlLean.TypeChecker.OwlTyping
import OwlLean.TypeChecker.OwlBuiltins
import Lean
import Std.Data.HashMap

open Owl
open Lean Elab Meta

structure Sequent where
  l : Nat
  r : Nat
  d : Nat
  m : Nat
  ref_vars : Vec.vec String r
  Phi : lbl_ctx (ScopeMap.ofList [l])
  Psi : corr_ctx (ScopeMap.ofList [l])
  Delta : ty_var_ctx (ScopeMap.ofList [l, r, d])
  Theta : prop_ctx (ScopeMap.ofList [l, r])
  Gamma : tm_ctx (ScopeMap.ofList [l, r, d, m])
  e : tm (ScopeMap.ofList [l, r, d, m])
  t : Option (ty (ScopeMap.ofList [l, r, d]))


def reportSuccess : TermElabM Unit := do
  let msgData := .tagged `goalsAccomplished m!"Goals accomplished!"
  log msgData (severity := .information) (isSilent := true)

def doTc (n : TSyntax `ident) (s : Sequent) := do
  let env : Env (ScopeMap.ofList [s.l, s.r, s.d, s.m]) := {
    defName := n.getId,
    ref_vars := s.ref_vars,
    lbl := s.Phi
    corrs := s.Psi,
    ty_vars := s.Delta,
    hyps := s.Theta,
    tms := s.Gamma
    curSyntax := none }

  match ← ReaderT.run (infer s.e s.t) env with
  | .ok tres => do
    println! "Successfully checked {n}"
    if s.t.isNone then println! "Inferred type: {tres.pretty}"
    reportSuccess
    let eTy <- mkAppM ``tm #[
      <- mkAppM ``ScopeMap.ofList #[toExpr [s.l, s.r, s.d, s.m]]
    ]
    emitDefinition n.getId eTy (toExpr $ s.e)
  | .err e => do
    logError s!"err: {e.2}"
    match e.1 with
    | .none => PURE
    | .some v =>
      logErrorAt v.inner e.2

def doCheckDecls (decl : Decl (ScopeMap.ofList [0, 0, 0, 0]) se) : TermElabM Unit :=  do
  let env : Env (ScopeMap.ofList [0, 0, 0, 0]) := {
    defName := Name.anonymous,
    ref_vars := .nil,
    lbl := .nil,
    corrs := .nil,
    ty_vars := .nil,
    hyps := .nil,
    tms := .nil,
    curSyntax := none
  }
  match ← ReaderT.run (checkDecls decl) env with
  | .ok _ => do
    reportSuccess
  | .err e =>
    match e.1 with
    | .none => PURE
    | .some v =>
      logErrorAt v.inner e.2


instance : OfNat (Fin ([A].length)) 0 where
  ofNat := by simp; exact 0

instance : OfNat (Fin ([A, B, C].length)) 2 where
  ofNat := by simp; exact 2

instance : OfNat (Fin ([A, B, C, D].length)) 3 where
  ofNat := by simp; exact 3

declare_syntax_cat label_entry

syntax ident owl_cond_sym owl_label : label_entry
syntax "corr" "(" owl_label ")" : label_entry
syntax "¬" "corr" "(" owl_label ")" : label_entry

syntax ident : label_entry

inductive label_entry_result (s : ScopeMap 1) where
  | new_label : String -> cond_sym -> label s -> label_entry_result s
  | corruption : corruption s -> label_entry_result s

def elabLabelEntry (stx : TSyntax `label_entry) (L : TCtx) : TermElabM (label_entry_result (ScopeMap.ofList [L.length])) :=
  match stx with
  | `(label_entry | $n:ident) => do
       let cs := cond_sym.geq
       let l := label.latl Owl.LabelTm.bot
       return .new_label (n.getId.toString) cs l
  | `(label_entry | $n:ident $cs:owl_cond_sym $lbl:owl_label ) => do
      let cs <- elabCondSym cs
      let l <- elabLabel lbl L
      return .new_label (n.getId.toString) cs l
  | `(label_entry | corr ($lbl:owl_label)) => do
      let l <- elabLabel lbl L
      return .corruption (.corr l)
  | `(label_entry | ¬ corr ($lbl:owl_label)) => do
      let l <- elabLabel lbl L
      return .corruption (.not_corr l)
  | _ => throwUnsupportedSyntax



def elabLabelEntries (stx : List (TSyntax `label_entry)) (L : TCtx) (ctx : lbl_ctx (ScopeMap.ofList [L.length])) (corrs : corr_ctx (ScopeMap.ofList [L.length])): TermElabM ((L' : TCtx) × lbl_ctx (ScopeMap.ofList [L'.length]) × corr_ctx (ScopeMap.ofList [L'.length])) :=
  match stx with
  | [] => return ⟨L, ctx, corrs⟩
  | e :: es => do
    match ← elabLabelEntry e L with
    | .new_label n cs l => do
      let l' : label ((ScopeMap.ofList [L.length + 1])) := l.rename (((ScopeMap.ofList [L.length]).lift #L))
      let L' := n :: L
      let ctx' : lbl_ctx (ScopeMap.ofList [L'.length]) :=
        Vec.vec.cons (n, (cs, l')) (ctx.map fun _ (n, (c, l)) => (n, (c, l.rename (((ScopeMap.ofList [L.length]).lift #L)))))
      let corrs' : corr_ctx (ScopeMap.ofList [L'.length]) :=
        corrs.map fun c => c.rename (((ScopeMap.ofList [L.length]).lift #L))
      elabLabelEntries es L' ctx' corrs'
    | .corruption c => do
      elabLabelEntries es L ctx (c :: corrs)


def elabRvarEntries (stx : List (TSyntax `ident)) (L : TCtx) (R : TCtx) : TermElabM (TCtx) :=
  match stx with
  | [] => return R
  | e :: es => do
    let R' := e.getId.toString :: R
    elabRvarEntries es L R'

declare_syntax_cat ty_var_entry

syntax ident "<:" owl_type : ty_var_entry

def elabTyVarEntry (stx : TSyntax `ty_var_entry) (L : TCtx) (R : TCtx) (D : TCtx) : TermElabM (String × ty (ScopeMap.ofList [L.length, R.length, D.length])) :=
  match stx with
  | `(ty_var_entry | $n:ident <: $t:owl_type ) => do
    let t <- elabType t L R D
    return (n.getId.toString, t)
  | _ => throwUnsupportedSyntax

def elabTyVarEntries (stx : List (TSyntax `ty_var_entry)) (L : TCtx) (R : TCtx) (D : TCtx) (ctx : ty_var_ctx (ScopeMap.ofList [L.length, R.length, D.length])) : TermElabM ((D' : TCtx) × ty_var_ctx (ScopeMap.ofList [L.length, R.length, D'.length])) :=
  match stx with
  | [] => return ⟨D, ctx⟩
  | e :: es => do
    let (n, t) <- elabTyVarEntry e L R D
    let t' := t.rename (((ScopeMap.ofList [L.length, R.length, D.length]).lift #Ty))
    let D' := n :: D
    let ctx' : ty_var_ctx (ScopeMap.ofList [L.length, R.length, D'.length]) :=
       Vec.vec.cons (n, t') (ctx.map fun _ (n, t) => (n, t.rename (((ScopeMap.ofList [L.length, R.length, D.length]).lift #Ty))))
    elabTyVarEntries es L R D' ctx'

declare_syntax_cat tm_entry

syntax ident ":" owl_type : tm_entry

def elabTmEntry (stx : TSyntax `tm_entry) (L : TCtx) (R : TCtx) (D : TCtx)  : TermElabM (String × ty (ScopeMap.ofList [L.length, R.length, D.length])) :=
  match stx with
  | `(tm_entry | $n:ident : $t:owl_type ) => do
    let t <- elabType t L R D
    return (n.getId.toString, t)
  | _ => throwUnsupportedSyntax

def elabTmEntries (stx : List (TSyntax `tm_entry)) (L : TCtx) (R : TCtx) (D : TCtx) (M : TCtx) (ctx : tm_ctx (ScopeMap.ofList [L.length, R.length, D.length, M.length])) : TermElabM ((G' : TCtx) × tm_ctx (ScopeMap.ofList [L.length, R.length, D.length, G'.length])) :=
  match stx with
  | [] => return ⟨M, ctx⟩
  | e :: es => do
    let (n, t) <- elabTmEntry e L R D
    let M' := n :: M
    let ctx' : tm_ctx (ScopeMap.ofList [L.length, R.length, D.length, M'.length]) :=
       Vec.vec.cons (n, t) ctx
    elabTmEntries es L R D M' ctx'

declare_syntax_cat owl_tc_ann
syntax owl_type : owl_tc_ann
syntax "?" : owl_tc_ann

def elabTcAnn (stx : TSyntax `owl_tc_ann) (L R D : TCtx) : TermElabM (Option (ty (ScopeMap.ofList [L.length, R.length, D.length]))) :=
  match stx with
  | `(owl_tc_ann | $t:owl_type) => do
    let t <- elabType t L R D
    return some t
  | `(owl_tc_ann | ?) => return none
  | _ => throwUnsupportedSyntax

elab "#tc" n:ident "[" lvars:(label_entry),* "]" "[" rvars:ident,* "]" "[" tvars:ty_var_entry,* "]" "[" tms:tm_entry,* "]" ":=" "⊢" "{" e:owl_tm "}" ":" t:owl_tc_ann : command => do
  Command.liftTermElabM $ withEnableInfoTree false do
    let lvars := lvars.getElems.toList
    let ⟨L, Lctx, corrs⟩ <- elabLabelEntries lvars [] .nil []
    let rvars := rvars.getElems.toList
    let R <- elabRvarEntries rvars L []
    let tvars := tvars.getElems.toList
    let ⟨D, Dctx⟩ <- elabTyVarEntries tvars L R [] .nil
    let ⟨M, Mctx⟩ <- elabTmEntries tms.getElems.toList L R D [] .nil
    let tmE ← elabTm e L R D M
    let tyE ← elabTcAnn t L R D
    let seq : Sequent := {
      l := L.length
      r := R.length
      d := D.length
      m := M.length
      Phi := Lctx
      Psi := corrs
      ref_vars := Vec.vec.ofList R
      Delta := Dctx
      Theta := .nil
      Gamma := Mctx
      e := tmE
      t := tyE
    }
    doTc n seq


elab "#tc" n:ident ":=" "⊢" "{" e:owl_tm "}" ":" t:owl_tc_ann : command => do
  Command.elabCommand (← `(#tc $n [] [] [] [] := ⊢ { $e } : $t))

elab "#ty" n:ident "[" lvars:ident,* "]" "[" rvars:ident,* "]" "[" tvars:ident,* "]" ":=" t:owl_type : command => do
  let lvars := lvars.getElems.toList.map (·.getId.toString)
  let rvars := rvars.getElems.toList.map (·.getId.toString)
  let tvars := tvars.getElems.toList.map (·.getId.toString)
  Command.liftTermElabM $ withEnableInfoTree false do
    let t <- elabType t lvars rvars tvars
    emitDefinition n.getId
       (<- mkAppM ``ty #[
          <- mkAppM ``ScopeMap.ofList #[ toExpr [lvars.length, rvars.length, tvars.length] ]
       ])
       (toExpr t)
    reportSuccess


elab "#ty" n:ident ":=" t:owl_type : command => do
  Command.elabCommand (← `(#ty $n [] [] [] := $t))

elab "#owl" "{" decls:owl_decl "}" : command => do
  Command.liftTermElabM $ withEnableInfoTree false do
    let ⟨_, decls⟩ <- elabDecls decls
    doCheckDecls decls

-- Example (must live in a downstream module so `command_elab` from `elab` above is active):
-- #tc foo := ⊢ { 32 } : Public
