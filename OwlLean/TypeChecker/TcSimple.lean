import OwlLean.TypeChecker.OwlTyping
import OwlLean.TypeChecker.OwlBuiltins
import OwlLean.OwlLang.ToString
import OwlLean.OwlLang.ScopeMap

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic
open Vec

mutual

@[simp]
def Owl.ty.simplify (t : ty s) (corrs : corr_ctx (s.restrict _)) : ty s :=
  match t with
  | .admit => t
  | .var_ty _ _ => t
  | .Any => t
  | .Unit => t
  | .RData _ _ => t
  | .Data _ => t
  | .Public => t
  | .refined t p => .refined (t.simplify corrs) p
  | .Ref t0 => .Ref t0
  | .arr t0 t1 => .arr (t0.simplify corrs) (t1.simplify corrs)
  | .union t0 t1 => .union (t0.simplify corrs) (t1.simplify corrs)
  | .inter t0 t1 => .inter (t0.simplify corrs) (t1.simplify corrs)
  | .ex t0 t1 => .ex (t0.simplify corrs) (t1.simplify (corrs.cast (by simp [ScopeMap.bump_restrict_ge])))
  | .ex_r t0 => .ex_r (t0.simplify (corrs.cast (by simp [ScopeMap.bump_restrict_ge])))
  | .all_r t0 => .all_r (t0.simplify (corrs.cast (by simp [ScopeMap.bump_restrict_ge])))
  | .all t0 t1 => .all (t0.simplify corrs) (t1.simplify (corrs.cast (by simp [ScopeMap.bump_restrict_ge])))
  | .t_if l t0 t1 =>
    match List.find? (fun corr =>
      match corr with
      | .corr l' => l == l'
      | .not_corr l' => l == l') corrs with
    | .none => .t_if l (t0.simplify $ (.corr l) :: corrs) (t1.simplify $ (.not_corr l) :: corrs)
    | .some corr => match corr with
      | .corr _ => t0.simplify corrs
      | .not_corr _ => t1.simplify corrs
  | .sum t0 t1 => .sum (t0.simplify corrs) (t1.simplify corrs)
  | .prod t0 t1 => .prod (t0.simplify corrs) (t1.simplify corrs)
  | .all_l cs l t => .all_l cs l (t.simplify (ScopeMap.bump_restrict _ _ _ _ ▸  corrs.bumpLbl))
  | .record s0 => .record (s0.simplify corrs)

def Owl.ty_record.simplify (r : ty_record s) (corrs : corr_ctx (s.restrict _)) : ty_record s :=
  match r with
  | .nil => .nil
  | .cons s t r => .cons s (t.simplify corrs) (r.simplify corrs)
end


namespace Owl

-- abbrev RCtx n := List (prop n 0)


inductive SideCondition : ScopeMap 2 -> Type where
  | PropHolds : prop s -> SideCondition s
  | LblEntails : lbl_ctx (s.restrict 1) -> Owl.constr (s.restrict _) -> SideCondition s
  | PhiPsiEntailCorr : String -> lbl_ctx (s.restrict _) -> corr_ctx (s.restrict _) -> corruption (s.restrict _) -> SideCondition s
  | LblContextInconsistent : String -> lbl_ctx (s.restrict _) -> corr_ctx (s.restrict _) -> SideCondition s
  | RexpEq : rexp s -> rexp s -> SideCondition s
  | WithLabel : cond_sym -> label (s.restrict _) -> SideCondition (s.bump #L) -> SideCondition s
  | ScOr : SideCondition s -> SideCondition s -> SideCondition s
  | ScAnd : SideCondition s -> SideCondition s -> SideCondition s
  | ScTrue : SideCondition s
  | ScFalse : SideCondition s
deriving ToExpr

abbrev SideCondition.cast {s t : ScopeMap 2} (h : s = t := by simp) (sc : SideCondition s) : SideCondition t := h ▸ sc

abbrev constr.cast {s t : ScopeMap 1} (h : s = t) (c : constr s) : constr t := h ▸ c


def SideCondition.pretty (p : SideCondition s) : String :=
  match p with
  | .PropHolds p => p.pretty
  | .LblEntails phi c => s!"({repr phi} |= {repr c})"
  | .PhiPsiEntailCorr msg phi psi co => s!"(phi, psi |= {repr co})"
  | .LblContextInconsistent msg phi psi => s!"(psi_context_inconsistent {msg})"
  | .RexpEq re1 re2 => s!"({repr re1} == {repr re2})"
  | .WithLabel cs lab sc => s!"({cs}, {lab} -> {sc.pretty})"
  | .ScOr e1 e2 => s!"({pretty e1} ∨ {pretty e2})"
  | .ScFalse => "false"
  | .ScTrue => "true"
  | .ScAnd e1 e2 => s!"{pretty e1} ∧ {pretty e2}"

/-

def SideCondition.pretty (p : SideCondition r) : String :=
  match p with
  | SideCondition.PhiEntails phi c => s!"({repr phi} |= {repr c})"
  | SideCondition.PhiPsiEntailCorr msg phi psi co => s!"(phi, psi |= {repr co})"
  | SideCondition.TyVarEq x y => s!"(TyVarEq {toString x} == {toString y})"
  | SideCondition.TyEq t1 t2 => s!"(TyEq {toString t1} == {toString t2})"
  | SideCondition.CondSymEq c1 c2 => s!"(CondSymEq {toString c1} == {toString c2})"
  | SideCondition.PsiContextInconsistent msg phi psi => s!"(psi_context_inconsistent {msg})"
  | SideCondition.RexpEq re1 re2 => s!"({repr re1} == {repr re2})"
  | SideCondition.PropHolds p1 => s!"(PropHolds {repr p1})"
  | SideCondition.ScOr e1 e2 => s!"({pretty e1} ∨ {pretty e2})"
  | SideCondition.ScAnd e1 e2 => s!"({pretty e1} ∧ {pretty e2})"
  | SideCondition.ScTrue => "True"
  | SideCondition.ScFalse => "False"

-/

instance : ToString (SideCondition r) where
  toString := SideCondition.pretty




inductive Result ε α where
  | ok : α -> Result ε α
  | err : ε -> Result ε α

abbrev prop_ctx s := List (prop s)

def prop_ctx.pretty {s : ScopeMap 2} (ctx : prop_ctx s) : String :=
  match ctx with
  | [] => "·"
  | ps => String.intercalate "; " (ps.map prop.pretty)

instance {s : ScopeMap 2} : ToString (prop_ctx s) where
  toString := prop_ctx.pretty

def prop_ctx.cast {s t : ScopeMap 2} (h : s = t) (p : prop_ctx s) : prop_ctx t :=
  h ▸ p

instance (ε : Type) : Monad (Result ε) where
  pure x := .ok x
  bind c k :=
    match c with
    | .ok x => k x
    | .err e => .err e



structure Env (s : ScopeMap 4) where
  defName : Name
  lbl : lbl_ctx (s.restrict _)
  ref_vars : Vec.vec String (s.get #R)
  corrs : corr_ctx (s.restrict _)
  ty_vars : ty_var_ctx (s.restrict _)
  hyps : prop_ctx (s.restrict _)
  tms :  tm_ctx s
  curSyntax : Option Owl.opaqueSyntax
  deriving ToExpr


structure SideConditionWithContext where
  s : ScopeMap 2
  hyps : prop_ctx s
  sc : SideCondition s
  deriving ToExpr


abbrev CheckT' s (α : Type) :=
  ReaderT (Env s) TermElabM (Result (Option Owl.opaqueSyntax × String) α)


@[always_inline, simp]
instance {s} : Monad (CheckT' s) where
  pure x := fun _ => pure (.ok x)
  bind c k := fun env => do
    match ← c env with
    | .err e => pure (.err e)
    | .ok x => do
      match ← k x env with
      | .err e2 => pure (.err e2)
      | .ok res => pure (.ok res)

instance : MonadReaderOf (Env s) (CheckT' s) where
  read := fun env => pure (.ok env)

def printTyCtx : CheckT' s String := do
  let env ← read
  let prettyTys := env.tms.toList.map fun (n, t) => s!"    {n}: {t.pretty}"
  let prettyHyps := env.hyps.map fun p => s!"    {p.pretty}"
  let prettyCorrs := env.corrs.map fun c => s!"    {c.pretty}"
  pure (String.intercalate "\n" (prettyTys ++ ["Path condition: "] ++ prettyHyps ++ ["Corruption: "] ++ prettyCorrs))

def throw' (s : String) : CheckT' sc α := do
  let tyErr := s!"Type error: {s}\nType context: \n {<- printTyCtx}"
  fun env => pure (.err (env.curSyntax, tyErr))


-- def lift_RCtx_r (θ : RCtx n) : RCtx (n + 1) :=
--   θ.map (ren_prop shift id)

def ScopeMap.renaming.cast (r : ScopeMap.renaming s t) (h1 : s = s') (h2 : t = t') : ScopeMap.renaming s' t' :=
  h2 ▸ h1 ▸ r

def ScopeMap.renaming.castR (r : ScopeMap.renaming s t) (h : t = t') : ScopeMap.renaming s t' :=
  h ▸ r

def ScopeMap.renaming.castL (r : ScopeMap.renaming s t) (h : s = s') : ScopeMap.renaming s' t :=
  h ▸ r

/-- Extend `gamma` with one term variable (its typing is at type index `0`). -/
def withTmVar {s : ScopeMap 4} (n : String) (t : ty (s.restrict 3)) (body : CheckT' (s.bump #Tm) α) : CheckT' s α :=
  fun env => body { env with
    lbl := (ScopeMap.bump_restrict _ _ _ _ ▸ env.lbl)
    corrs := (ScopeMap.bump_restrict _ _ _ _ ▸ env.corrs)
    ref_vars := env.ref_vars.castLength (by simp)
    ty_vars := env.ty_vars.cast (by rw [ScopeMap.bump_restrict]; grind)
    hyps := env.hyps.cast (by rw [ScopeMap.bump_restrict]; grind)
    tms := (Vec.vec.cons (n, t) (env.tms)).cast (by simp) (by rw [ScopeMap.bump_restrict]; grind)
   }

def withHypsAppend {s} (hyps : List (prop (s.restrict _))) (body : CheckT' s α) : CheckT' s α :=
  fun env => body { env with hyps := env.hyps ++ hyps }

def withCorruption {s} (c : corruption (s.restrict _)) (body : CheckT' s α) : CheckT' s α :=
  fun env => body { env with corrs := c :: env.corrs }





def withTyVar {s : ScopeMap 4} (n : String) (t0 : ty (s.restrict 3)) (body : CheckT' (s.bump #Ty) α) : CheckT' s α :=
  fun env =>
    body { env with
      lbl := (env.lbl.castLength (by simp)).castTy (by simp [ScopeMap.bump_restrict])
      corrs := cast (by simp [ScopeMap.bump_restrict]) env.corrs,
      ty_vars := (vec.castCons (n, t0.rename ((s.lift #Ty).restrict (by simp)))
                            (env.ty_vars.map fun _ (n, t) => (n, t.rename ((s.lift #Ty).restrict (by simp)))) (by simp))
      hyps := cast (by congr 1; rw [ScopeMap.bump_restrict]; grind ) env.hyps
      ref_vars := env.ref_vars.castLength (by simp)
      tms := (env.tms.map fun _ (n', t) => (n', t.rename ((s.lift #Ty).restrict _))).cast (by simp) (by congr 1)
    }

def withRefVar {s} (nm : String) (body : CheckT' (s.bump #R) α) : CheckT' s α :=
  fun env =>
    body {
      env with
      lbl := (env.lbl.castLength (by simp)).castTy (by simp [ScopeMap.bump_restrict])
      corrs := cast (by simp [ScopeMap.bump_restrict]) env.corrs,
      ty_vars := (env.ty_vars.map fun _ (n, t) => (n, t.rename ((s.lift #R).restrict _))).castLength (by simp),
      hyps := env.hyps.map fun p => p.rename ((s.lift #R).restrict (by simp)),
      tms := (env.tms.map fun _ (n, t) => (n, t.rename ((s.lift #R).restrict _))).cast (by simp) (by congr 1)
      ref_vars := (vec.castCons nm env.ref_vars (by simp))
    }

def Env.addRef {s : ScopeMap 4} (nm : String) (env : Env s) : Env (s.bump #R) :=
    {
      env with
      lbl := (env.lbl.castLength (by simp)).castTy (by simp [ScopeMap.bump_restrict])
      corrs := cast (by simp [ScopeMap.bump_restrict]) env.corrs,
      ty_vars := (env.ty_vars.map fun _ (n, t) => (n, t.rename ((s.lift #R).restrict _))).castLength (by simp),
      hyps := env.hyps.map fun p => p.rename ((s.lift #R).restrict (by simp)),
      tms := (env.tms.map fun _ (n, t) => (n, t.rename ((s.lift #R).restrict _))).cast (by simp) (by congr 1)
      ref_vars := (vec.castCons nm env.ref_vars (by simp))
    }


def withLabelVar [Monad m] (cs : cond_sym) (n : String) (lab : label (s.restrict _)) (ty : lbl_type) (body : ReaderT (Env (s.bump #L)) m α) : ReaderT (Env s) m α :=
  fun env =>
    body {
   env with
      lbl := (vec.castCons (n, (cs, lab.rename ((s.lift #L).restrict _), ty))
                           (env.lbl.map fun _ (n, (c, l, ty)) => (n, (c, l.rename ((s.lift #L).restrict (by simp)), ty)))
                           (by simp))
      corrs := env.corrs.map fun c => c.rename ((s.lift #L).restrict (by simp))
      ty_vars := (env.ty_vars.map fun _ (n, t) => (n, t.rename ((s.lift #L).restrict _))).castLength (by simp),
      hyps := env.hyps.map fun p => p.rename ((s.lift #L).restrict (by simp))
      tms := (env.tms.map fun _ (n, t) => (n, t.rename ((s.lift #L).restrict _))).cast (by simp) (by congr 1)
      ref_vars := env.ref_vars.castLength (by simp)
  }


-- def withUnpackBinders {l r d m α} (t0 : ty l r d 0) (t : ty l r (d + 1) 0)
--     (body : CheckT' l r (d + 1) (m + 1) α) : CheckT' l r d m α :=
--   fun env =>
--     body { env with delta := lift_delta (cons t0 env.delta), gamma := cons t (lift_gamma_d env.gamma) }


attribute [simp] Fin.foldr_succ


mutual
@[simp]
def rexp.interp {s : ScopeMap 2}
  (re : rexp s)
  (f_interp : String -> List OwlVal -> OwlVal )
  (fv : Lean.Name -> OwlVal)
  (bv : vec OwlVal (s.get #R))
  : OwlVal :=
  match re with
  | .fvar nm => fv nm
  | .var i => bv.get (i.cast $ by simp)
  | .op s rs =>
    let rs_interp := rs.interp f_interp fv bv
    f_interp s rs_interp
  | .const b => b

@[simp]
def rexp_list.interp {s : ScopeMap 2}
  (rs : rexp_list s)
  (f_interp : String -> List OwlVal -> OwlVal )
  (fv : Lean.Name -> OwlVal)
  (bv : vec OwlVal (s.get #R))
  : List OwlVal :=
  match rs with
  | .nil => []
  | .cons r rs => r.interp f_interp fv bv :: rs.interp f_interp fv bv

end


abbrev prop.cast {s t : ScopeMap 2} (h : s = t := by simp) (l : prop s) : prop t := h ▸ l

abbrev label.cast {s t : ScopeMap 1} (h : s = t := by simp) (l : label s) : label t := h ▸ l

abbrev corruption.cast {s t : ScopeMap 1} (h : s = t := by simp)  (c : corruption s) : corruption t := h ▸ c

abbrev ty.cast {s t : ScopeMap 3} (h : s = t := by simp) (T : ty s) : ty t := h ▸ T

abbrev rexp.cast {s t : ScopeMap 2} (h : s = t := by simp) (T : rexp s) : rexp t := h ▸ T


@[grind =]
theorem SideCondition.cast_sizeOf {s t : ScopeMap 2} (h : s = t) (sc : SideCondition s) : sizeOf (SideCondition.cast h sc) = sizeOf sc := by
  cases h
  simp

@[grind =]
theorem corruption.cast_sizeOf {s t : ScopeMap 1} (h : s = t) (c : corruption s) : sizeOf (corruption.cast h c) = sizeOf c := by
  cases h
  simp

@[grind =]
theorem prop.cast_sizeOf {s t : ScopeMap 2} (h : s = t ) (l : prop s) : sizeOf (prop.cast h l) = sizeOf l := by
  cases h
  simp

@[grind =]
theorem label.cast_sizeOf {s t : ScopeMap 1} (h : s = t) (l : label s) : sizeOf (label.cast h l) = sizeOf l := by
  cases h
  simp





@[simp]
def prop.interp {s : ScopeMap 2}
(p : prop s)
(f_interp : String -> List OwlVal -> OwlVal)
(fv : Lean.Name -> OwlVal)
(bv : vec OwlVal (s.get #R))
: Prop :=
  match p with
  | .ptrue => True
  | .peq re1 re2 =>
     let r1_interp : OwlVal := re1.interp f_interp fv bv
     let r2_interp : OwlVal := re2.interp f_interp fv bv
     r1_interp = r2_interp
  | .pand p1 p2 =>
     let p1_interp : Prop := p1.interp f_interp fv bv
     let p2_interp : Prop := p2.interp f_interp fv bv
     p1_interp ∧ p2_interp
  | .por p1 p2 =>
     let p1_interp : Prop := p1.interp f_interp fv bv
     let p2_interp : Prop := p2.interp f_interp fv bv
     p1_interp ∨ p2_interp
  | .pimpl p1 p2 =>
     let p1_interp : Prop := p1.interp f_interp fv bv
     let p2_interp : Prop := p2.interp f_interp fv bv
     p1_interp → p2_interp
  | .pnot p1 =>
     let p1_interp : Prop := p1.interp f_interp fv bv
     ¬ p1_interp
  | .pall p1 =>
    let p1_interp := p1.interp f_interp
    forall fv v, p1_interp fv ((vec.cons v bv).castLength (by simp))



@[simp]
def prop_ctx.interp {s : ScopeMap 2}
  (hyps : prop_ctx s)
  (f_interp : String -> List OwlVal -> OwlVal)
  (fv : Lean.Name -> OwlVal)
  (bv : vec OwlVal (s.get #R))
  : Prop :=
  hyps.foldr (fun p acc => p.interp f_interp fv bv ∧ acc) True


@[simp]
def SideCondition.eval {s : ScopeMap 2} (p : SideCondition s)
(f_interp : String -> List OwlVal -> OwlVal)
(fv : Lean.Name -> OwlVal)
(bv : vec OwlVal (s.get #R))
: Prop :=
  match p with
  | LblEntails phi c => phi.entails c
  | PhiPsiEntailCorr _ phi psi l => entail_corr phi psi l
  | LblContextInconsistent _ phi psi => lbl_ctx.inconsistent_with phi psi
  | RexpEq r1 r2 => r1.interp f_interp fv bv = r2.interp f_interp fv bv
  | PropHolds p1 => p1.interp f_interp fv bv
  | ScOr e1 e2 =>
    let e1_interp := e1.eval f_interp fv bv
    let e2_interp := e2.eval f_interp fv bv
    e1_interp ∨ e2_interp
  | WithLabel cs lab e =>
    e.eval f_interp fv (bv.castLength (by simp))
  | ScAnd e1 e2 =>
    let e1_interp := e1.eval f_interp fv bv
    let e2_interp := e2.eval f_interp fv bv
    e1_interp ∧ e2_interp
  | ScTrue => True
  | ScFalse => False

attribute [simp] SideCondition.eval.eq_def

def CheckT'.liftPure (k : ReaderT (Env s) (Result String) α) : CheckT' s α :=
  fun env => do
    match ReaderT.run k env with
    | .ok x => pure (.ok x)
    | .err e => pure (.err (.none, e))

def CheckT'.liftTermElab (k : TermElabM α) : CheckT' s α :=
  fun _ => do
    let r <- k
    pure (.ok r)

namespace Proof

@[simp]
def SideConditionWithContext.eval (sc : SideConditionWithContext) : Prop :=
  let p1 := sc.hyps.interp owl_f_interp
  let p2 := sc.sc.eval owl_f_interp
  forall fv bv, p1 fv bv -> p2 fv bv

def runGrind (g : Expr) : TermElabM Bool := do
  -- let s <- Lean.PrettyPrinter.delab g
  -- log s!"runGrind: {<- Lean.PrettyPrinter.ppTerm s}" (severity := .information)
  let g <- mkFreshExprMVar g
  let res <- Grind.main g.mvarId! (<- Grind.mkDefaultParams {})
  return res.failure?.isNone

#check Simp.main

def doSimp (e : Expr) : TermElabM Expr := do
  let simpThms <- getSimpTheorems
  let congrThms <- getSimpCongrTheorems
  -- let simprocs <- Simp.getSimprocs
  let ctx <- Simp.mkContext (simpTheorems := #[simpThms]) (congrTheorems := congrThms)
  let methods <- Simp.mkDefaultMethods
  let res <- Simp.main e ctx (methods := methods)
  return res.fst.expr



end Proof

noncomputable def foo := 3

def emitDefinition (name : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← inferType value
  let fvars := (collectFVars {} value).fvarIds.map mkFVar
  let (type, value) ←
    if fvars.isEmpty then
      pure (type, value)
    else do
      let value ← mkLambdaFVars fvars value
      let type ← inferType value
      pure (type, value)
  let decl := Declaration.defnDecl {
    name        := name
    levelParams := []
    type        := type
    value       := value
    hints       := ReducibilityHints.abbrev
    safety      := DefinitionSafety.safe
  }
  addDecl decl
  compileDecl decl

 def decideProp {s : ScopeMap 4} (sc : SideCondition (s.restrict _)) : CheckT' s Bool := do
  let scc : SideConditionWithContext := {s := (s.restrict _), hyps := (<- read).hyps, sc := sc}
  let e  <- CheckT'.liftTermElab $ mkAppM ``Proof.SideConditionWithContext.eval #[toExpr scc]
  let e <- CheckT'.liftTermElab $ Proof.doSimp e
  CheckT'.liftTermElab $ do
  Proof.runGrind e


 def prove {s : ScopeMap 4} (sc : SideCondition (s.restrict _)) (errmsg : String) : CheckT' s Unit := do
  let defName := (<- read).defName
  let scName := Name.append defName `side_condition
  let scc : SideConditionWithContext := {s := (s.restrict _), hyps := (<- read).hyps, sc := sc}
  let e  <- CheckT'.liftTermElab $ mkAppM ``Proof.SideConditionWithContext.eval #[toExpr scc]
  let e <- CheckT'.liftTermElab $ Proof.doSimp e
  let b <- CheckT'.liftTermElab $ Proof.runGrind e
  if not b then
     CheckT'.liftTermElab $ emitDefinition scName e
     throw' s!"{errmsg}! Emitting side condition to {scName}"



def withSyntax'  (stx : Owl.opaqueSyntax) (k : CheckT' s α) : CheckT' s α :=
  fun env => k { env with curSyntax := .some stx }



def addTypeInfo (stx : Syntax) (s : String) := do
    let n : Name := Name.mkSimple s

    withEnableInfoTree true do withLocalDeclD n (mkSort levelOne) fun dslType => do
      let forgedExpr ← mkFreshExprMVar dslType
      pushInfoLeaf <| .ofTermInfo {
        elaborator := `Sequent
        stx := stx
        lctx := (← getLCtx)
        expectedType? := some dslType
        expr := forgedExpr
        isBinder := false
      }
    pure ()

def visit {s : ScopeMap 4} (stx : Owl.opaqueSyntax) (t : ty (s.restrict _)) : CheckT' s Unit := fun _ => do
  addTypeInfo stx.inner (toString t)
  pure (.ok ())

def log  (st : String) : CheckT' s Unit := fun _ => do
  println! st
  pure (.ok ())

def freshName  : CheckT' s Lean.Name := fun _ => do
  let i <- mkFreshId
  pure (.ok i)

abbrev subtype_fuel := 10



abbrev Scope := ScopeMap 4


partial def extract_refinements {s : Scope} (t : ty (s.restrict _)) : CheckT' s (prop_ctx (s.restrict _) × ty (s.restrict _)) :=
  match t with
  | .ex_r t0 => do -- ∃ x. t
    let i <- freshName
    let t1 := t0.subst (ScopeMap.Subst.down (rexp.fvar i))
    extract_refinements t1
  | .refined t p => do -- t { φ }
    let (x, y) <- extract_refinements t
    return ((p.cast) :: x, y)
  | .prod t1 t2 => do -- t1 * t2
    let (x, y) <- extract_refinements t1
    let (x', y') <- extract_refinements t2
    return (x ++ x', .prod y y')
  | _ => return ([], t)

-- instance [h : EqScopeMap s t] : CoeDep (lbl_ctx s) m (lbl_ctx t) where
--   coe := h.heq ▸ m
--
-- instance [h : EqScopeMap s t] : CoeDep (corr_ctx s) m (corr_ctx t) where
--   coe := h.heq ▸ m
--
-- instance [h : EqScopeMap s t] : CoeDep (SideCondition s) m (SideCondition t) where
--   coe := h.heq ▸ m
--
--
-- instance [h : EqScopeMap s t] : EqScopeMap t s where
--   heq := h.heq.symm
--
-- instance : IsTrue ((3 : Fin 4) >= 3) where
--   pf := by simp
--
-- instance : NeqFin (0 : Fin 4) (3 : Fin 4) where
--   h := by grind


def List.uniq? [DecidableEq α] (l : List α) : Bool :=
  match l with
  | [] => true
  | (x :: xs) => if x ∈ xs then false else uniq? xs

def List.sort_assocs (ls : List (String × α)) : List (String × α) :=
  ls.mergeSort (fun x y => x.1 < y.1)


def ty_record.mk (ls : List (String × ty s)) : ty_record s :=
  match ls with
  | [] => .nil
  | (s, t) :: ls => .cons s t (ty_record.mk ls)

def ty_record.toList (t : ty_record s) : List (String × ty s) :=
  match t with
  | .nil => []
  | .cons s t l => (s, t) :: l.toList

def check_corrupt {s : Scope} (lab : label (s.restrict _)) :
    CheckT' s (Option Bool) := do
  if (<- read).corrs.contains (.corr lab) then pure (.some True)
  else if ← decideProp (.PhiPsiEntailCorr s!"check_corrupt" ((<- read).lbl.cast (by simp)) ((<- read).corrs.cast (by simp)) (.corr (lab.cast (by simp))))
  then pure (.some True)
  else if (<- read).corrs.contains (.not_corr lab) then pure (.some False)
  else if ← decideProp (.PhiPsiEntailCorr s!"check_corrupt" ((<- read).lbl.cast (by simp)) ((<- read).corrs.cast (by simp)) (.not_corr (lab.cast (by simp))))
  then pure (.some False)
  else pure (.none)


-- Computes the side condition necessary for t1 <: t2
partial def check_subtype'  {s : Scope} (t1 t2 : ty (s.restrict _)) : CheckT' s (SideCondition (s.restrict _)) := do
  log s!"check_subtype': {t1.pretty} <: {t2.pretty}"
  if t1.erase_varname == t2.erase_varname then pure .ScTrue else
    let (pextract, t1) <- extract_refinements t1
    withHypsAppend pextract $ do
      match t1, t2 with
      | .admit, _ => pure .ScTrue
      | _, .Any => pure .ScTrue
      | .Unit, .Unit => pure .ScTrue
      | .record s0, .record s1 => do
        let s0 := s0.toList
        let s1 := s1.toList
        unless s0.map (·.1) |>.uniq? do throw' s!"mk_record: fields must be unique"
        unless s1.map (·.1) |>.uniq? do throw' s!"mk_record: fields must be unique"
        let s0 := s0.sort_assocs
        let s1 := s1.sort_assocs
        unless s0.map (·.1) = s1.map (·.1) do throw' s!"mk_record: fields must be the same"
        let s01 := s0.zip s1
        let rs <- s01.mapM fun (s, t) => do
           check_subtype' s.2 t.2
        pure (rs.foldl (fun r s => r.ScAnd s) .ScTrue)
      | .t_if lab ta1 ta2, t' => do
        match <- check_corrupt lab.cast with
        | some b => check_subtype' (if b then ta1 else ta2) t'
        | none => do
          let env ← read
          let r1 ← withCorruption (.corr (lab.cast)) (check_subtype' ta1 t')
          let r2 ← withCorruption (.not_corr (lab.cast)) (check_subtype' ta2 t')
          pure (r1.ScAnd r2)
      | t, .t_if lab ta1' ta2' => do
        match <- check_corrupt lab.cast with
        | some b => check_subtype' t (if b then ta1' else ta2')
        | none => do
          let env ← read
          let r1 ← withCorruption ((.corr (lab.cast))) (check_subtype' t ta1')
          let r2 ← withCorruption ((.not_corr (lab.cast))) (check_subtype' t ta2')
          pure (r1.ScAnd r2)
      | _, .refined t p => do
        let r1 ← check_subtype' t1 t
        pure (r1.ScAnd (.PropHolds (p.cast)))
      | _, .inter t21 t22 => do
        let r1 ← check_subtype' t1 t21
        let r2 ← check_subtype' t1 t22
        pure (r1.ScAnd r2)
      | _, .union t21 t22 => do
        let r1 ← check_subtype' t1 t21
        let r2 ← check_subtype' t1 t22
        pure (r1.ScOr r2)
      | .inter t11 t12, _ => do
        let r1 ← check_subtype' t11 t2
        let r2 ← check_subtype' t12 t2
        pure (r1.ScOr r2)
      | .RData l1 _, .Data l2 => do
        let env ← read
        pure (.LblEntails (env.lbl.cast) (.condition .leq (l1.cast) (l2.cast)))
      | .RData l1 re1, .RData l2 re2 => do
        let env ← read
        let r1 := SideCondition.LblEntails (env.lbl.cast) (.condition .leq (l1.cast) (l2.cast))
        let r2 := SideCondition.RexpEq re1 re2
        pure (r1.ScAnd (r2.cast))
      | .Public, .Data _ => pure .ScTrue
      | .Data l1, .Public => do
        let env ← read
        pure (.PhiPsiEntailCorr s!"Data {l1}, Public" (env.lbl.cast) (env.corrs.cast) (.corr (l1.cast)))
      | .Data l1, .Data l2 =>
        let env ← read
        pure (.LblEntails (env.lbl.cast) (.condition .leq (l1.cast) (l2.cast)))
      | .RData l1 _, .Public => do
        let env ← read
        pure (.PhiPsiEntailCorr s!"RData {l1}, Public" (env.lbl.cast) (env.corrs.cast) (.corr (l1.cast)))
      | .Data l1, ty.ex_r (.RData l2 (.var ⟨0, _⟩)) => do
        let env ← read
        pure (.LblEntails (env.lbl.cast)
                          (.condition .leq (l1.cast)
                          (l2.cast (by simp [ScopeMap.bump_restrict]))))
      | .var_ty _ x1, .var_ty _ x2 =>
        pure (if x1 = x2 then .ScTrue else .ScFalse)
      | .Public, .Public => pure .ScTrue
      | .var_ty _ x, t => do
        let tx := ((<- read).ty_vars.get x).2
        -- x <: tx
        -- tx <: t
        ----------
        -- x <: t
        check_subtype' tx t
      -- TODO: I deleted the case of (t <: .var_ty _ x).
      | (.arr ta1 ta2), (.arr ta1' ta2') => do
        let r1 ← check_subtype' ta1' ta1
        let r2 ← check_subtype' ta2 ta2'
        pure (r1.ScAnd r2)
      | (.prod ta1 ta2), (.prod ta1' ta2') => do
        let r1 ← check_subtype' ta1 ta1'
        let r2 ← check_subtype' ta2 ta2'
        pure (r1.ScAnd r2)
      | (.sum ta1 ta2), (.sum ta1' ta2') => do
        let r1 ← check_subtype' ta1 ta1'
        let r2 ← check_subtype' ta2 ta2'
        pure (r1.ScAnd r2)
      | .Ref u, .Ref v =>
        if u == v then pure .ScTrue else pure .ScFalse
      | .all t0 t, .all t0' t' => do
        let r1 ← check_subtype' t0' t0
        let r2 ← withTyVar "_" t0' (check_subtype' (t.cast (by simp [ScopeMap.bump_restrict])) (t'.cast (by simp [ScopeMap.bump_restrict])))
        pure (r1.ScAnd (r2.cast (by simp [ScopeMap.bump_restrict])))
      | .ex t0 t, .ex t0' t' => do
        let r1 ← check_subtype' t0 t0'
        let r2 ← withTyVar "_" t0 (check_subtype' (t.cast (by simp [ScopeMap.bump_restrict])) (t'.cast (by simp [ScopeMap.bump_restrict])))
        pure (r1.ScAnd (r2.cast (by simp [ScopeMap.bump_restrict])))
      | .all_l cs lab t, .all_l _cs' lab' t' => do
        unless cs = _cs' do throw' s!"check_subtype': cs and cs' are not equal"
        let env ← read
        let extPhi : lbl_ctx ((s.bump #L).restrict 1) :=
            (vec.cons ("_", cs, lab.rename (((s.lift #L).restrict _).restrict _), .QuantLbl)
                      (env.lbl.map fun _ (n, (sc, l, ty )) =>
                             (n, (sc, l.rename (by rw [ScopeMap.restrict_restrict]; exact ((s.lift #L).restrict _)), ty)))).cast
               (by simp)
               (by simp)
        let constraint : constr ((s.bump #L).restrict 1) := (.condition cs (.var_label "_" (by simp [ScopeMap.get]; exact 0))
                                (lab'.rename (by rw [ScopeMap.restrict_restrict]; exact ((s.lift #L).restrict _))))
        let r1 : SideCondition ((s.bump #L).restrict 2) :=
          SideCondition.LblEntails (extPhi.cast)
                                 (constraint.cast (by simp [ScopeMap.bump_restrict]))
        let r2 ← withLabelVar cs "_" (lab.cast) .QuantLbl (check_subtype' (t.cast (by simp [ScopeMap.bump_restrict])) (t'.cast (by simp [ScopeMap.bump_restrict])))
        pure (.WithLabel cs (lab.cast) ((r1.ScAnd r2).cast (by simp [ScopeMap.bump_restrict])))
      | _, _ => do
        let env ← read
        let sc : SideCondition (s.restrict _) := SideCondition.LblContextInconsistent "" (env.lbl.cast) (env.corrs.cast)
        CheckT'.liftTermElab $ emitDefinition `FOO (toExpr sc)
        log s!"sc: logged inconsistent to FOO"
        pure (.LblContextInconsistent s!"check_subtype': {t1} and {t2} are not comparable" (env.lbl.cast) (env.corrs.cast))

def check_subtype {s : Scope} (t1 t2 : ty (s.restrict _)) : CheckT' s Unit := do
  let sc ← check_subtype' t1 t2
  prove sc s!"Could not prove {t1.pretty} <: {t2.pretty}"

@[simp]
def from_synth {s : Scope} (t : ty (s.restrict _)) (exp : Option (ty (s.restrict _))) : CheckT' s (ty (s.restrict _)) :=
  match exp with
  | .none => pure t
  | .some t' => do
    check_subtype t t'
    pure t'

/-

  t : if corr(L) then t1 else t2

  corr_case L in
  ... t : t1 ...


-/

def lbl_type.join (t1 t2 : lbl_type) : lbl_type :=
  match t1, t2 with
  | .MetaLbl, _ => t2
  | _, .MetaLbl => t1
  | .QuantLbl, .QuantLbl => .QuantLbl

def label.inferTy {s : Scope} (l : label (s.restrict _)) : CheckT' s lbl_type := do
  match l with
  | .latl _ => pure .MetaLbl
  | .var_label _ x => do
    let (_, _, _, ty) := (<- read).lbl.get x
    pure ty
  | .ljoin l1 l2 => do
    let r1 ← label.inferTy l1
    let r2 ← label.inferTy l2
    pure (r1.join r2)
  | .lmeet l1 l2 => do
    let r1 ← label.inferTy l1
    let r2 ← label.inferTy l2
    pure (r1.join r2)

-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"

-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type

/-- Labels inside `ty (s.restrict 3)` use `label ((s.restrict 3).restrict 1)`. -/
private def ty.getLabel {s : Scope} (op : String) (t : ty (s.restrict 3)) :
    CheckT' s (label ((s.restrict 3).restrict 1)) :=
  match t with
  | .Public => pure (.latl LabelTm.bot)
  | .RData l _ => pure l
  | .Data l => pure l
  | _ => throw' s!"Error when checking builtin {op}: argument must be of type Data / RData / Public. Got {t.pretty}"

-- May have to return an arbitrary rexp if the type is not an RData
def ty.getRexp {s : Scope} (t : ty (s.restrict 3)) :
    CheckT' s (rexp ((s.restrict 3).restrict 2)) :=
  match t with
  | .RData _ r => pure r
  | .Data _ | .Public => do
      let i <- freshName
      pure (.fvar i)
  | _ => throw' s!"Error when obtaining rexp: argument must be of type RData / Data / Public. Got {t.pretty}"

-- TODO: finish here.
-- I have moved unop/binop to just "op" with a list.
-- I need to finish TcSimple and then finish the elaborator.

def infer_op {s : Scope} (op : String) (ts : List (ty (s.restrict _))) : CheckT' s (ty (s.restrict _)) := do
  let lbl_rexps <- ts.mapM fun t => do
    let l <- t.getLabel op
    let r <- t.getRexp
    pure (l, r)
  let lbl := (lbl_rexps.map (·.1)).foldl label.ljoin (.latl LabelTm.bot)
  let rexps := lbl_rexps.map (·.2)
  pure $ .RData lbl (.op op (rexp_list.mk rexps))

def rexp.mk_op (op : String) (rs : List (rexp s)) : rexp s :=
  .op op (rexp_list.mk rs)

mutual
partial def infer (e : tm s) (exp : Option (ty (s.restrict _))) : CheckT' s (ty (s.restrict _)) :=
  match e with
  | .mk stx v => do
    let t ← withSyntax' stx (inferX v exp)
    let corrs := (← read).corrs
    let t := t.simplify (corrs.cast)
    visit stx t
    return t


partial def inferX (e : tmX s) (exp : Option (ty (s.restrict _))) : CheckT' s (ty (s.restrict _))  :=
  match e with
  | .admit => from_synth .admit exp
  | .secparam => from_synth .Public exp
  | .get_record s0 s1 => do
    let t <- infer s1 .none
    match t with
    | .record r => do
      match r.toList.find? (fun (s, t) => s = s0) with
      | .some (s, t) => from_synth t exp
      | .none => throw' s!"get_record: field {s0} not found in record"
    | _ => throw' s!"get_record: expected record, got {t}"
  | .mk_record l => do
     let ls := l.toList
     unless ls.length > 1 do throw' s!"mk_record: expected at least one field"
     unless ls.map (·.1) |>.uniq? do throw' s!"mk_record: fields must be unique"
     let ls := ls.sort_assocs
     let ls <- ls.mapM fun (s, e) => do
      let t <- infer e .none
      pure (s, t)
     from_synth (.record (ty_record.mk ls)) exp
  | .sample e => do
    let t ← infer e .none
    let tInf <- match t with
                | .Public | .Data _ => pure .Public
                | .RData _ r =>
                  let r : rexp (s.restrict 2) := r.cast
                  let peq : prop ((s.restrict 2).bump #R) :=
                    .peq (rexp.mk_op "zero" [r.rename $ ((s.lift #R).restrict _).castR (by simp [ScopeMap.restrict_bump])])
                         (rexp.mk_op "zero" [.var ⟨0, by simp [ScopeMap.restrict_bump]⟩])
                  let r' : ty ((s.restrict 3)) :=
                    ty.ex_r $ .refined
                      (.RData (.latl LabelTm.bot) (.var ⟨0, by simp [ScopeMap.restrict_bump]⟩))
                      (peq.cast (by simp [ScopeMap.bump_restrict]))
                  pure r'
                | _ => throw' s!"Error when checking sample: did not get a bitstring; got {t}"
    from_synth tInf exp

  | .var_tm x => do
    from_synth ((<- read).tms.get x).2 exp
  | .unit => from_synth .Unit exp
  | .bitstring b => from_synth (.RData (.latl LabelTm.bot) (.const b)) exp
  | .get_val rname e t => do
     let t0 <- infer e .none
     let r <- t0.getRexp
     let r' : rexp ((s.bump #R).restrict 2) :=
      r.rename $ ((s.lift #R).restrict _).castL (by simp)
     withRefVar rname $
       withHypsAppend [.peq r' (.var ⟨0, by simp⟩ )] $ do
        let res <- infer t (exp.map fun t => t.rename ((s.lift #R).restrict _))
        let res : (ty ((s.restrict 3).bump #R)) := res.cast (by simp [ScopeMap.bump_restrict])
        pure $ res.subst (ScopeMap.Subst.down r)
  | .op op es => do
    let ts <- es.toList.mapM (fun x => infer x.2 none)
    let res <- infer_op op ts
    from_synth res exp
  | .zero e => do
    let t ← infer e none
    match t with
    | .Public | .Data _ | .RData _ _ => from_synth .Public exp
    | _ => throw' s!"Error when checking zero: did not get a bitstring; got {t}"
  | .if_tm e e1 e2 => do
    let _ ← infer e (.some .Public)
    let t1 ← infer e1 exp
    let t2 ← infer e2 exp
    check_subtype t2 t1
    from_synth t1 exp
  | .tlet x e1 e2 => do
    let t1 ← infer e1 .none
    let (theta', t1') ← extract_refinements t1
    let res <- withTmVar x t1' $ withHypsAppend (theta'.cast (by simp [ScopeMap.bump_restrict]; grind)) (infer e2 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
    from_synth (res.cast (by simp [ScopeMap.bump_restrict]; grind)) exp
  | .union_elim x e1 e2 => do
    let t1 ← infer e1 .none
    match t1 with
    | .union t11 t12 => do
      let res1 ← withTmVar x t11 (infer e2 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
      let res2 ← withTmVar x t12 (infer e2 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
      if res1 == res2 then from_synth (res1.cast (by simp [ScopeMap.bump_restrict]; grind)) exp
      else throw' "union_elim: must get same type on both sides"
    | _ => do
        let res <- withTmVar x t1 (infer e2 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
        pure $ res.cast (by simp [ScopeMap.bump_restrict]; grind)
  | .alloc e => do
    let t ← infer e .none
    from_synth (.Ref t) exp
  | .dealloc e => do
    let t ← infer e .none
    match t with
    | .Ref t0 => from_synth t0 exp
    | _ => throw' "dealloc"
  | .assign e1 e2 => do
    let t0 ← infer e1 .none
    match t0 with
    | .Ref t1 => do
      let _ ← infer e2 (.some t1)
      from_synth .Unit exp
    | _ => throw' "assign"
  | .inl e =>
    match exp with
    | .some (.sum t1 t2) => do
      let _ ← infer e (.some t1)
      pure (.sum t1 t2)
    | _ => throw' "inl: need annotation for full type"
  | .inr e =>
    match exp with
    | .some (.sum t1 t2) => do
      let _ ← infer e (.some t2)
      pure (.sum t1 t2)
    | _ => throw' "inr: need annotation for full type"
  | .fixlam nm1 nm2 e =>
    match exp with
    | .some (.arr t t') => do
      let expected := (t'.cast (by simp [ScopeMap.bump_restrict]; grind))
      let _ ← withTmVar nm2 t (withTmVar nm1 ((ty.arr t t').cast (by simp [ScopeMap.bump_restrict]; grind)) (infer e (.some expected)))
      pure (.arr t t')
    | _ => throw' "λ : need type annotation either on binder or on output type "
  | .app e1 e2 =>
    match exp with
    | .none => do
      match ← infer e1 .none with
      | .arr t t' => do
        let _ ← infer e2 (.some t)
        pure t'
      | t => throw' s!"app: got unexpected type for function: {t} "
    | .some expected => do
      let t1 ← infer e2 .none
      let _ ← infer e1 (.some (.arr t1 expected))
      pure expected
  | .tm_pair e1 e2 => do
    let t1 ← infer e1 .none
    let t2 ← infer e2 .none
    from_synth (.prod t1 t2) exp
  | .left_tm e => do
    match ← infer e .none with
    | .prod t1 _ => from_synth t1 exp
    | t => throw' s!"π1: got unexpected type: {ty.pretty t}"
  | .right_tm e => do
    match ← infer e .none with
    | .prod _ t2 => from_synth t2 exp
    | t => throw' s!"π2: got unexpected type: {ty.pretty t}"
  | .case e x e1 y e2 => do
    match ← infer e .none with
    | .sum t1 t2 => do
      let r1 ← withTmVar x t1 (infer e1 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
      let r2 ← withTmVar y t2 (infer e2 (exp.map fun t => t.cast (by simp [ScopeMap.bump_restrict]; grind)))
      match exp with
      | .some res => return res
      | none => do
        check_subtype (r2.cast (by simp [ScopeMap.bump_restrict]; grind)) (r1.cast (by simp [ScopeMap.bump_restrict]; grind))
        pure (r1.cast (by simp [ScopeMap.bump_restrict]; grind))
    | t => throw' s!"Case: need sum type, but got {t.pretty}"
  | .rlam nm e =>
    match exp with
    | .some (.all_r t0) => do
      let _ ← withRefVar nm (infer e (.some (t0.cast (by simp [ScopeMap.bump_restrict]))))
      pure (.all_r t0)
    | _ => throw' "Error when type checking Λr: expected type must be of the form ∀ x. τ"
  | .tlam x e =>
    match exp with
    | .some (.all t0 t) => do
      let _ ← withTyVar x t0 (infer e (.some (t.cast (by simp [ScopeMap.bump_restrict]))))
      pure (.all t0 t)
    | _ => throw' s!"Error when type checking Λ: expected type must be a ∀. Instead, got {exp} "
  | .rapp e re => do
    -- let re' ← resolve_re re
    match ← infer e .none with
    | .all_r t0 => do
      let result_ty := t0.subst (ScopeMap.Subst.down re.cast)
      --(subst_ty (.var_label "_") (cons re' .var) .var_ty t0
      from_synth result_ty exp
    | _ => throw' "rapp: expected type must be of the form ∀r x. τ"
  | .tapp e t' => do
    -- let t'' ← resolve_ty t'
    match ← infer e .none with
    | .all t0 t => do
      check_subtype t' t0
      let result_ty := t.subst (ScopeMap.Subst.down t')
      from_synth result_ty exp
    | _ => throw' "tapp"
  | .rpack re e => do
    -- let re' ← resolve_re re
    match exp with
    | .some (.ex_r t0) => do
      let substituted_type := t0.subst (ScopeMap.Subst.down re.cast)
      let _ ← infer e (.some substituted_type)
      pure (.ex_r t0)
    | _ => throw' "rpack: need expected type of form rpack(r, e)"
  | .pack t' e => do
    -- let t' ← resolve_ty t'
    match exp with
    | .none => throw' "pack: empty expected"
    | .some (.ex t0 t) => do
      let substituted_type := t.subst (ScopeMap.Subst.down t')
      check_subtype t' t0
      let _ ← infer e (.some substituted_type)
      pure (.ex t0 t)
    | _ => throw' "pack"
  | .unpack e tx x e' =>
    match exp with
    | .none => throw' "unpack: empty expected"
    | .some exp_ty => do
      match ← infer e .none with
      | .ex t0 t => do
        let renamed_t' := (exp_ty.rename ((s.lift #Ty).restrict _))
        let _ ← withTyVar tx t0 (withTmVar x (t.cast (by simp [ScopeMap.bump_restrict]))
                             (infer e' (.some (renamed_t'.cast (by simp [ScopeMap.bump_restrict]; grind)))))
        pure exp_ty
      | _ => throw' "unpack"
  | .l_lam nm e =>
    match exp with
    | .none => throw' "l_lam: empty expected"
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body => do
        let _ ← withLabelVar cs nm lab.cast .QuantLbl (infer e (.some $ t_body.cast (by simp [ScopeMap.bump_restrict])))
        pure exp_ty
      | _ => throw' "l_lam"
  | .lapp e lab' => do
    let t ← label.inferTy lab'
    unless t = .MetaLbl do throw' s!"lapp: label {lab'} cannot arise from a quantifier"
    match exp with
    | .none => do
      let env ← read
      match ← infer e .none with
      | .all_l cs lab t => do
        let result_ty := t.subst (ScopeMap.Subst.down lab'.cast)
        prove (.LblEntails ((<- read).lbl.cast) (.condition cs lab.cast lab'.cast))
          s!"lapp: could not prove |= {cs} {lab} {lab'}"
        pure result_ty
      | _ => throw' "lapp"
    | .some exp_ty => do
      let env ← read
      match ← infer e .none with
      | .all_l cs lab t => do
        let result_ty := t.subst (ScopeMap.Subst.down lab'.cast)
        check_subtype result_ty exp_ty
        prove (.LblEntails ((<- read).lbl.cast) (.condition cs lab.cast lab'.cast))
          s!"lapp: could not prove |= {cs} {lab} {lab'}"
        pure exp_ty
      | _ => throw' "lapp"
  | .annot e t' => do
    -- let t' ← resolve_ty t'
    let r ← infer e (.some t')
    from_synth r exp
  | .if_c lab e1 e2 => do
    let env ← read
    let t1 ← withCorruption (.corr $ lab.cast) (infer e1 exp)
    let t2 ← withCorruption (.not_corr $ lab.cast) (infer e2 exp)
    from_synth (.t_if (lab.cast) t1 t2) exp
  | .corr_case lab e => do
    match ← check_corrupt (lab.cast) with
    | .none => do
      let env ← read
      let t1 ← withCorruption (.corr $ lab.cast) (infer e exp)
      let t2 ← withCorruption (.not_corr $ lab.cast) (infer e exp)
      match exp with
      | .none => pure (.t_if (lab.cast) t1 t2)
      | .some exp_ty => pure exp_ty
    | .some b => withCorruption (if b then (.corr $ lab.cast) else (.not_corr $ lab.cast)) (infer e exp)
  | .loc _ => throw' "infer: unhandled case"
end

def checkDecl (decl : Decl s1 s2) (k : CheckT' s2 α) : CheckT' s1 α := do
  match decl with
  | .Nil => k
  | .DeclTy name ty => withTyVar name.toString ty k
  | .DeclTm name tm ot => do
     let t <- ReaderT.adapt (fun e => {e with defName := name}) $ infer tm ot
     withTmVar name.toString t k
  | .DeclTmAssume name t => withTmVar name.toString t k
  | .DeclLabel name cs lab => withLabelVar cs name.toString lab .MetaLbl k
  | .DeclApp d1 d2 => do
    checkDecl d1 (checkDecl d2 k)

def checkDecls (decl : Decl s1 s2) := checkDecl decl (pure ())

end Owl
