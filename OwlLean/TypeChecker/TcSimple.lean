import OwlLean.TypeChecker.OwlTyping
import OwlLean.OwlLang.ToString

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic

@[simp]
def Owl.ty.simplify (t : ty l r d m ) (corrs : List (corruption l)): ty l r d m :=
  match t with
  | .admit => t
  | .var_ty _ => t
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
  | .ex t0 t1 => .ex (t0.simplify corrs) (t1.simplify corrs)
  | .ex_r t0 => .ex_r (t0.simplify corrs)
  | .all_r t0 => .all_r (t0.simplify corrs)
  | .all t0 t1 => .all (t0.simplify corrs) (t1.simplify corrs)
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
  | .default => .default
  | .all_l cs l t => .all_l cs l (t.simplify $ lift_psi corrs)


namespace OwlTc


abbrev RCtx n := List (prop n 0)


inductive SideCondition r where
  | PhiEntails : phi_context_repr l -> Owl.constr l -> SideCondition r
  | PhiPsiEntailCorr : String -> phi_context_repr l -> psi_context l -> corruption l -> SideCondition r
  | TyVarEq : Fin d -> Fin d -> SideCondition r
  | TyEq : ty l r d m -> ty l r d m -> SideCondition r
  | CondSymEq : cond_sym -> cond_sym -> SideCondition r
  | PsiContextInconsistent : String -> phi_context_repr l -> psi_context l -> SideCondition r
  | RexpEq : rexp r 0 -> rexp r 0 -> SideCondition r
  | PropHolds : prop r 0 -> SideCondition r
  | ScOr : SideCondition r -> SideCondition r -> SideCondition r
  | ScAnd : SideCondition r -> SideCondition r -> SideCondition r
  | ScTrue
  | ScFalse
deriving ToExpr


@[simp]
def rexp_interp (re : rexp r 0) (bvar_interp : Fin r -> String) (fvar_interp : Lean.Name -> String) (f_interp : String -> String -> String -> String )  :=
  match re with
  | .var i => bvar_interp i
  | .op s r1 r2 => f_interp s (rexp_interp r1 bvar_interp fvar_interp f_interp) (rexp_interp r2 bvar_interp fvar_interp f_interp)
  | .const b => b
  | .fvar i => fvar_interp i

@[simp]
def interp_prop (p : prop r 0) (bvar_interp : Fin r -> String) (fvar_interp : Lean.Name -> String) (f_interp : String -> String -> String -> String) :=
  match p with
  | .peq re1 re2 => (rexp_interp re1 bvar_interp fvar_interp f_interp) = (rexp_interp re2 bvar_interp fvar_interp f_interp)
  | .pand p1 p2 => interp_prop p1 bvar_interp fvar_interp f_interp ∧ interp_prop p2 bvar_interp fvar_interp f_interp
  | .por p1 p2 => interp_prop p1 bvar_interp fvar_interp f_interp ∨  interp_prop p2 bvar_interp fvar_interp f_interp
  | .pimpl p1 p2 => interp_prop p1 bvar_interp fvar_interp f_interp → interp_prop p2 bvar_interp fvar_interp f_interp
  | .pnot p1 => ¬ interp_prop p1 bvar_interp fvar_interp f_interp
  | .pall p1 =>
    forall v,
    interp_prop p1 (cons v bvar_interp) fvar_interp f_interp



@[simp]
def SideCondition.eval (p : SideCondition r) (bvar_interp : Fin r -> String) (fvar_interp : Lean.Name -> String) (f_interp : String -> String -> String -> String) : Prop :=
  match p with
  | PhiEntails phi c => vec.to_fn phi |= c
  | PhiPsiEntailCorr _ phi psi l => phi_psi_entail_corr (vec.to_fn phi) psi l
  | TyVarEq x y => x = y
  | TyEq t1 t2 => t1 = t2
  | CondSymEq c1 c2 => c1 = c2
  | PsiContextInconsistent _ phi psi => psi_context_inconsistent (vec.to_fn phi) psi
  | RexpEq re1 re2 => (rexp_interp re1 bvar_interp fvar_interp f_interp) = (rexp_interp re2 bvar_interp fvar_interp f_interp)
  | PropHolds p1 => interp_prop p1 bvar_interp fvar_interp f_interp
  | ScOr e1 e2 => e1.eval bvar_interp fvar_interp f_interp ∨ e2.eval bvar_interp fvar_interp f_interp
  | ScAnd e1 e2 => e1.eval bvar_interp fvar_interp f_interp ∧  e2.eval bvar_interp fvar_interp f_interp
  | ScTrue => True
  | ScFalse => False

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

instance : ToString (SideCondition r) where
  toString := SideCondition.pretty

@[simp]
def RCtx.interp (theta : RCtx r) (bvar_interp : Fin r -> String) (fvar_interp : Lean.Name -> String) (f_interp : String -> String -> String -> String) : Prop :=
  List.foldr (fun i acc => interp_prop i bvar_interp fvar_interp f_interp ∧ acc) True theta


inductive Result ε α where
  | ok : α -> Result ε α
  | err : ε -> Result ε α

structure SideConditionWithContext where
  r : Nat
  theta : RCtx r
  sc : SideCondition r
  deriving ToExpr


structure Env l r d m where
  phi : phi_context l
  psi : psi_context l
  delta : delta_context l r d
  theta : RCtx r
  gamma : gamma_context l r d m
  curSyntax : Option Owl.opaqueSyntax



abbrev CheckT' l r d m (α : Type) :=
  ReaderT (Env l r d m) TermElabM (Result (Option Owl.opaqueSyntax × String) α)

@[always_inline, simp]
instance {l r d m} : Monad (CheckT' l r d m) where
  pure x := fun _ => pure (.ok x)
  bind c k := fun env => do
    match ← c env with
    | .err e => pure (.err e)
    | .ok x => do
      match ← k x env with
      | .err e2 => pure (.err e2)
      | .ok res => pure (.ok res)

def lift_RCtx_r (θ : RCtx n) : RCtx (n + 1) :=
  θ.map (ren_prop shift id)

/-- Extend `gamma` with one term variable (its typing is at type index `0`). -/
def withGammaVar {l r d m α} (t : ty l r d 0) (body : CheckT' l r d (m + 1) α) : CheckT' l r d m α :=
  fun env => body { env with gamma := cons t env.gamma }

/-- Extend `theta` and `gamma` as in `tlet` after `extract_refinements`. -/
def withThetaAppendAndGammaVar {l r d m α} (θs : RCtx r) (t : ty l r d 0)
    (body : CheckT' l r d (m + 1) α) : CheckT' l r d m α :=
  fun env => body { env with theta := env.theta ++ θs, gamma := cons t env.gamma }

def withPsi {l r d m α} (ψ : psi_context l) (body : CheckT' l r d m α) : CheckT' l r d m α :=
  fun env => body { env with psi := ψ }

def withDeltaTyVar {l r d m α} (t0 : ty l r d 0) (body : CheckT' l r (d + 1) m α) : CheckT' l r d m α :=
  fun env =>
    body { env with delta := lift_delta (cons t0 env.delta), gamma := lift_gamma_d env.gamma }

def withRefLevel {l r d m α} (body : CheckT' l (r + 1) d m α) : CheckT' l r d m α :=
  fun env =>
    body {
      env with
      delta := lift_delta_r env.delta
      theta := lift_RCtx_r env.theta
      gamma := lift_gamma_r env.gamma }

def withLabelVar {l r d m α} (cs : cond_sym) (lab : label l) (body : CheckT' (l + 1) r d m α) :
    CheckT' l r d m α :=
  fun env =>
    body {
      env with
      phi := lift_phi (cons (cs, lab) env.phi)
      psi := lift_psi env.psi
      delta := lift_delta_l env.delta
      gamma := lift_gamma_l env.gamma }

def withUnpackBinders {l r d m α} (t0 : ty l r d 0) (t : ty l r (d + 1) 0)
    (body : CheckT' l r (d + 1) (m + 1) α) : CheckT' l r d m α :=
  fun env =>
    body { env with delta := lift_delta (cons t0 env.delta), gamma := cons t (lift_gamma_d env.gamma) }


attribute [simp] Fin.foldr_succ

namespace Proof

opaque owl_f_interp' : String -> String -> String -> String

def owl_f_interp (s x y : String) : String :=
  match s with
  | "concat" => x ++ y
  | _ => owl_f_interp' s x y

@[simp]
def SideConditionWithContext.eval (sc : SideConditionWithContext) : Prop :=
  forall bv fv, RCtx.interp sc.theta bv fv owl_f_interp -> sc.sc.eval bv fv owl_f_interp

def runGrind (g : Expr) : TermElabM Bool := do
  let g <- mkFreshExprMVar g
  let res <- Grind.main g.mvarId! (<- Grind.mkDefaultParams {})
  return res.failure?.isNone


def doSimp (e : Expr) : TermElabM Expr := do
  let ctx <- Simp.Context.mkDefault
  let res <- Lean.Meta.simp e ctx
  return res.fst.expr


 def doGrindSc {r} (theta : RCtx r) (sc : SideCondition r) : TermElabM Bool := do
  let scc : SideConditionWithContext := {r := r, theta := theta, sc := sc}
  let e  <- mkAppM ``SideConditionWithContext.eval #[toExpr scc]
  let e <- doSimp e
  -- logInfo s!"doGrindSc: simped to {<- PrettyPrinter.ppExpr e}"
  runGrind e

end Proof

instance {l r d m} : MonadReaderOf (Env l r d m) (CheckT' l r d m) where
  read := fun env => pure (.ok env)

def prove  (p : SideCondition r) : CheckT' l r d m Bool :=
  fun env => .ok <$> Proof.doGrindSc env.theta p

def printTyCtx : CheckT' l r d m String := do
  let env ← read
  let g_repr := vec.from_fn env.gamma
  let pretties := g_repr.toList.map fun t => s!"    {t.pretty}"
  pure (String.intercalate "\n" pretties)


def throw' {l r d m α} (s : String) : CheckT' l r d m α := do
  let tyErr := s!"Type error: {s}\nType context: \n {<- printTyCtx}"
  fun env => pure (.err (env.curSyntax, tyErr))

def withSyntax' {l r d m α} (s : Owl.opaqueSyntax) (k : CheckT' l r d m α) : CheckT' l r d m α :=
  fun env => k { env with curSyntax := .some s }



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

def visit {l r d m} (s : Owl.opaqueSyntax) (t : ty l r d 0) : CheckT' l r d m Unit := fun _ => do
  addTypeInfo s.inner (toString t)
  pure (.ok ())

def log {l r d m} (s : String) : CheckT' l r d m Unit := fun _ => do
  println! s
  pure (.ok ())

def freshName {l r d m} : CheckT' l r d m Lean.Name := fun _ => do
  let i <- mkFreshId
  pure (.ok i)

abbrev subtype_fuel := 10



-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!


partial def extract_refinements {l r d m} (t : ty l r d 0) : CheckT' l r d m (RCtx r × ty l r d 0) :=
  match t with
  | .ex_r t0 => do -- ∃ x. t
    let i <- freshName
    let t1 := t0.subst_rexp i
    extract_refinements t1
  | .refined t p => do -- t { φ }
    let (x, y) <- extract_refinements t
    return (p :: x, y)
  | .prod t1 t2 => do -- t1 * t2
    let (x, y) <- extract_refinements t1
    let (x', y') <- extract_refinements t2
    return (x ++ x', .prod y y')
  | _ => return ([], t)


-- Computes the side condition necessary for t1 <: t2
partial def check_subtype' {l r d m : Nat} (t1 t2 : ty l r d 0) : CheckT' l r d m (SideCondition r) := do
  log s!"check_subtype': {t1.pretty} <: {t2.pretty}"
  if t1 == t2 then pure .ScTrue else
    match t1, t2 with
    | .admit, _ => pure .ScTrue
    | _, .Any => pure .ScTrue
    | .Unit, .Unit => pure .ScTrue
    | _, .refined t p => do
      let r1 ← check_subtype' t1 t
      pure (r1.ScAnd (.PropHolds p))
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
      pure (.PhiEntails (vec.from_fn env.phi) (.condition .leq l1 l2))
    | .RData l1 re1, .RData l2 re2 => do
      let env ← read
      let r1 := SideCondition.PhiEntails (vec.from_fn env.phi) (.condition .leq l1 l2)
      let r2 := SideCondition.RexpEq re1 re2
      pure (r1.ScAnd r2)
    | .Data l1, .Public => do
      let env ← read
      pure (.PhiPsiEntailCorr s!"Data {l1}, Public" (vec.from_fn env.phi) env.psi (.corr l1))
    | .Data l1, .Data l2 =>
      let env ← read
      pure (.PhiEntails (vec.from_fn env.phi) (.condition .leq l1 l2))
    | .RData l1 _, .Public => do
      let env ← read
      pure (.PhiPsiEntailCorr s!"RData {l1}, Public" (vec.from_fn env.phi) env.psi (.corr l1))
    | .Data l1, ty.ex_r (.RData l2 (.var 0)) => do
      let env ← read
      pure (.PhiEntails (vec.from_fn env.phi) (.condition .leq l1 l2))
    | .var_ty x1, .var_ty x2 =>
      pure (.TyVarEq x1 x2)
    | .Public, .Public => pure .ScTrue
    | .var_ty x, t' => do
      let env ← read
      check_subtype' (env.delta x) t'
    | t, .var_ty x => do
      let env ← read
      check_subtype' t (env.delta x)
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
      pure (.TyEq u v)
    | .all t0 t, .all t0' t' => do
      let r1 ← check_subtype' t0 t0'
      let r2 ← withDeltaTyVar t0' (check_subtype' t t')
      pure (r1.ScAnd r2)
    | .ex t0 t, .ex t0' t' => do
      let r1 ← check_subtype' t0 t0'
      let r2 ← withDeltaTyVar t0 (check_subtype' t t')
      pure (r1.ScAnd r2)
    | .all_l cs lab t, .all_l _cs' lab' t' => do
      let env ← read
      let extPhi := lift_phi (cons (cs, lab) env.phi)
      let constraint := (.condition cs (.var_label "_" var_zero) (ren_label shift lab'))
      let r1 := SideCondition.PhiEntails (vec.from_fn extPhi) constraint
      let r2 ← withLabelVar cs lab (check_subtype' t t')
      pure (r1.ScAnd r2)
    | .t_if lab ta1 ta2, t' => do
      let env ← read
      let r1 ← withPsi ((.corr lab) :: env.psi) (check_subtype' ta1 t')
      let r2 ← withPsi ((.not_corr lab) :: env.psi) (check_subtype' ta2 t')
      pure (r1.ScAnd r2)
    | t, .t_if lab ta1' ta2' => do
      let env ← read
      let r1 ← withPsi ((.corr lab) :: env.psi) (check_subtype' t ta1')
      let r2 ← withPsi ((.not_corr lab) :: env.psi) (check_subtype' t ta2')
      pure (r1.ScAnd r2)
    | _, _ => do
      let env ← read
      pure (.PsiContextInconsistent s!"check_subtype': {t1} and {t2} are not comparable" (vec.from_fn env.phi) env.psi)

def check_subtype {l r d m} (t1 t2 : ty l r d 0) : CheckT' l r d m Unit := do
  let sc ← check_subtype' t1 t2
  let b ← prove sc
  if b then pure ()
  else throw' s!"Could not prove {t1.pretty} <: {t2.pretty} (side condition: {sc.pretty})"

@[simp]
def from_synth {l r d m} (t : ty l r d 0) (exp : Option (ty l r d 0)) : CheckT' l r d m (ty l r d 0) :=
  match exp with
  | .none => pure t
  | .some t' => do
    check_subtype t t'
    pure t'

def check_corrupt {l r d m} (lab : label l) :
    CheckT' l r d m (Option Bool) := do
  if (<- read).psi.contains (.corr lab) then pure (.some True)
  else if ← prove (.PhiPsiEntailCorr s!"check_corrupt" (vec.from_fn (<- read).phi) (<- read).psi (.corr lab))
  then pure (.some True)
  else if (<- read).psi.contains (.not_corr lab) then pure (.some False)
  else if ← prove (.PhiPsiEntailCorr s!"check_corrupt" (vec.from_fn (<- read).phi) (<- read).psi (.not_corr lab))
  then pure (.some False)
  else pure (.none)

/-

  t : if corr(L) then t1 else t2

  corr_case L in
  ... t : t1 ...


-/


-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"

-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type

def infer_op {l r d m} (op : String) (t1 t2 : ty l r d 0) : CheckT' l r d m (ty l r d 0) := do
  let env ← read
  match t1, t2 with
  | .RData l1 r1, .RData l2 r2 => do
    let b ← prove (.PhiEntails (vec.from_fn env.phi) (.condition .leq l2 l1))
    if b then pure (.RData l1 (.op op r1 r2))
    else throw' "infer_op: could not prove Phi |= l2 <= l1"
  | .Public, .Public => return .Public
  | _, _ => do
    let getLabel (t : ty l r d 0) : CheckT' l r d m (label l) :=
      match t with
      | .Public => return .latl L.bot
      | .RData l _ => return l
      | .Data l => return l
      | _ => throw' "infer_op: argument must be of type Data / RData / Public"
    let l1 ← getLabel t1
    let l2 ← getLabel t2
    return (.Data (label.ljoin l1 l2))

def resolve_ty {l r d m} (t : ty l r d m) : CheckT' l r d m (ty l r d 0) := do
  let env ← read
  t.resolve_tm fun i =>
    match env.gamma i with
    | ty.RData _ a => return a
    | _ => throw' s!"Refinement expression or prop cannot make reference to non-refinfed variable"

def resolve_re {l r d m} (t : rexp r m) : CheckT' l r d m (rexp r 0) := do
  let env ← read
  t.resolve_tm fun i =>
    match env.gamma i with
    | ty.RData _ a => return a
    | _ => throw' s!"Refinement expression or prop cannot make reference to non-refinfed variable"


mutual
def infer {l r d m} (e : tm l r d m) (exp : Option (ty l r d 0)) : CheckT' l r d m (ty l r d 0) :=
  match e with
  | .mk stx v => do
    let t ← withSyntax' stx (inferX v exp)
    let psi := (← read).psi
    let t := t.simplify psi
    visit stx t
    return t

def inferX {l r d m} (e : tmX l r d m) (exp : Option (ty l r d 0)) : CheckT' l r d m (ty l r d 0) :=
  match e with
  | .admit => from_synth .admit exp
  | .var_tm x => do
    from_synth ((<- read).gamma x) exp
  | .skip => from_synth .Unit exp
  | .bitstring b => from_synth (.RData (.latl L.bot) (.const b)) exp
  | .Op op e1 e2 => do
    let t1 ← infer e1 .none
    let t2 ← infer e2 .none
    let tres ← infer_op op t1 t2
    from_synth tres exp
  | .zero e => do
    let t ← infer e none
    match t with
    | .Public | .Data _ | .RData _ _ => from_synth .Public exp
    | _ => throw' "zero: not bitstring"
  | .if_tm e e1 e2 => do
    let _ ← infer e (.some .Public)
    let t1 ← infer e1 exp
    let t2 ← infer e2 exp
    check_subtype t2 t1
    from_synth t1 exp
  | .tlet e1 e2 => do
    let t1 ← infer e1 .none
    let (theta', t1') ← extract_refinements t1
    withThetaAppendAndGammaVar theta' t1' (infer e2 exp)
  | .union_elim e1 e2 => do
    let t1 ← infer e1 .none
    match t1 with
    | .union t11 t12 => do
      let res1 ← withGammaVar t11 (infer e2 exp)
      let res2 ← withGammaVar t12 (infer e2 exp)
      if res1 == res2 then return res1
      else throw' "union_elim: must get same type on both sides"
    | _ => withGammaVar t1 (infer e2 exp)
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
  | .fixlam _ e =>
    match exp with
    | .some (.arr t t') => do
      let _ ← withGammaVar t (withGammaVar (.arr t t') (infer e (.some t')))
      pure (.arr t t')
    | _ => throw' "fixlam"
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
  | .case e e1 e2 => do
    match ← infer e .none with
    | .sum t1 t2 => do
      let r1 ← withGammaVar t1 (infer e1 exp)
      let r2 ← withGammaVar t2 (infer e2 exp)
      match exp with
      | .some res => return res
      | none => do
        check_subtype r2 r1
        pure r1
    | _ => throw' "case"
  | .rlam e =>
    match exp with
    | .some (.all_r t0) => do
      let _ ← withRefLevel (infer e (.some t0))
      pure (.all_r t0)
    | _ => throw' "Error when type checking Λr: expected type must be of the form ∀ x. τ"
  | .tlam e =>
    match exp with
    | .some (.all t0 t) => do
      let _ ← withDeltaTyVar t0 (infer e (.some t))
      pure (.all t0 t)
    | _ => throw' s!"Error when type checking Λ: expected type must be a ∀. Instead, got {exp} "
  | .rapp e re => do
    let re' ← resolve_re re
    match ← infer e .none with
    | .all_r t0 => do
      let result_ty := subst_ty (.var_label "_") (cons re' .var) .var_ty t0
      from_synth result_ty exp
    | _ => throw' "rapp: expected type must be of the form ∀r x. τ"
  | .tapp e t' => do
    let t'' ← resolve_ty t'
    match ← infer e .none with
    | .all t0 t => do
      check_subtype t'' t0
      let result_ty := subst_ty (.var_label "_") .var (cons t'' .var_ty) t
      from_synth result_ty exp
    | _ => throw' "tapp"
  | .rpack re e => do
    let re' ← resolve_re re
    match exp with
    | .some (.ex_r t0) => do
      let substituted_type := subst_ty (.var_label "_") (cons re' .var) .var_ty t0
      let _ ← infer e (.some substituted_type)
      pure (.ex_r t0)
    | _ => throw' "rpack: need expected type of form rpack(r, e)"
  | .pack t' e => do
    let t' ← resolve_ty t'
    match exp with
    | .none => throw' "pack: empty expected"
    | .some (.ex t0 t) => do
      let substituted_type := subst_ty (.var_label "_") .var (cons t' .var_ty) t
      check_subtype t' t0
      let _ ← infer e (.some substituted_type)
      pure (.ex t0 t)
    | _ => throw' "pack"
  | .unpack e e' =>
    match exp with
    | .none => throw' "unpack: empty expected"
    | .some exp_ty => do
      match ← infer e .none with
      | .ex t0 t => do
        let renamed_t' := ren_ty id id shift id exp_ty
        let _ ← withUnpackBinders t0 t (infer e' (.some renamed_t'))
        pure exp_ty
      | _ => throw' "unpack"
  | .l_lam e =>
    match exp with
    | .none => throw' "l_lam: empty expected"
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body => do
        let _ ← withLabelVar cs lab (infer e (.some t_body))
        pure exp_ty
      | _ => throw' "l_lam"
  | .lapp e lab' =>
    match exp with
    | .none => do
      let env ← read
      match ← infer e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        let b ← prove (.PhiEntails (vec.from_fn (<- read).phi) (.condition cs lab lab'))
        if b then pure result_ty
        else throw' "lapp: could not prove Phi |= cs lab lab'"
        pure result_ty
      | _ => throw' "lapp"
    | .some exp_ty => do
      let env ← read
      match ← infer e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        check_subtype result_ty exp_ty
        let b ← prove (.PhiEntails (vec.from_fn (<- read).phi) (.condition cs lab lab'))
        if b then pure exp_ty
        else throw' "lapp: could not prove Phi |= cs lab lab'"
        pure exp_ty
      | _ => throw' "lapp"
  | .annot e t' => do
    let t' ← resolve_ty t'
    let r ← infer e (.some t')
    from_synth r exp
  | .if_c lab e1 e2 => do
    let env ← read
    let t1 ← withPsi ((.corr lab) :: env.psi) (infer e1 none)
    let t2 ← withPsi ((.not_corr lab) :: env.psi) (infer e2 none)
    from_synth (.t_if lab t1 t2) exp
  | .corr_case lab e => do
    match ← check_corrupt lab with
    | .none => do
      let env ← read
      let t1 ← withPsi ((.corr lab) :: env.psi) (infer e exp)
      let t2 ← withPsi ((.not_corr lab) :: env.psi) (infer e exp)
      match exp with
      | .none => pure (.t_if lab t1 t2)
      | .some exp_ty => pure exp_ty
    | .some _ => infer e exp
  | .sync e => do
    let _ ← infer e (.some .Public)
    from_synth .Public exp
  | .default => throw' "infer: unhandled case"
  | .loc _ => throw' "infer: unhandled case"
  | .error => throw' "infer: unhandled case"
end


syntax "split_grind" : tactic

macro_rules
  | `(tactic| split_grind) => `(tactic|
      first
      | (constructor <;> split_grind)
      | grind)

end OwlTc
