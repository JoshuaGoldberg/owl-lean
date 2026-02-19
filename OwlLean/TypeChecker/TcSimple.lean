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


/-
-- Useful TODO
theorem Owl.ty.simplify_rec_sound (phi : phi_context l) (psi : psi_context l) delta (t : ty l d) :
  subtype phi psi delta t (t.simplify psi) ∧ subtype phi psi delta (t.simplify psi) t := by
    revert psi
    induction t <;> intros psi <;> simp  <;> try apply subtype.ST_Refl
    constructor <;> apply subtype.ST_Func <;> grind only
    constructor <;> apply subtype.ST_Prod <;> grind only
    constructor <;> apply subtype.ST_Sum <;> grind only
    constructor <;> apply subtype.ST_Univ <;> grind only
    constructor <;> apply subtype.ST_Exist <;> grind only
    constructor
    apply subtype.ST_LatUniv
    {
      intros pm Hpm
      sorry
    }
    sorry
    apply subtype.ST_LatUniv
    sorry
    sorry

    sorry

  -/


















namespace OwlTc


abbrev RCtx n := List (prop n 0)


inductive SideCondition r where
  | PhiEntails : phi_context_repr l -> Owl.constr l -> SideCondition r
  | PhiPsiEntailCorr : String -> phi_context_repr l -> psi_context l -> label l -> SideCondition r
  | TyVarEq : Fin d -> Fin d -> SideCondition r
  | TyEq : ty l r d m -> ty l r d m -> SideCondition r
  | CondSymEq : cond_sym -> cond_sym -> SideCondition r
  | PsiContextInconsistent : String -> phi_context_repr l -> psi_context l -> SideCondition r
  | RexpEq : rexp r 0 -> rexp r 0 -> SideCondition r
  | PropHolds : prop r 0 -> SideCondition r
deriving ToExpr

instance : ToString (SideCondition r) where
  toString := fun _ => "<sc>"


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



-- TODO: ToString for SideCondition.

-- TODO next: We want fvar_interp and f_interp to be global and implicitly universally quantified.
-- we can just make them opaque.
-- But
@[simp]
def SideCondition.eval (p : SideCondition r) (bvar_interp : Fin r -> String) (fvar_interp : Lean.Name -> String) (f_interp : String -> String -> String -> String) : Prop :=
  match p with
  | PhiEntails phi c => vec.to_fn phi |= c
  | PhiPsiEntailCorr _ phi psi l => phi_psi_entail_corr (vec.to_fn phi) psi (.corr l)
  | TyVarEq x y => x = y
  | TyEq t1 t2 => t1 = t2
  | CondSymEq c1 c2 => c1 = c2
  | PsiContextInconsistent _ phi psi => psi_context_inconsistent (vec.to_fn phi) psi
  | RexpEq re1 re2 => (rexp_interp re1 bvar_interp fvar_interp f_interp) = (rexp_interp re2 bvar_interp fvar_interp f_interp)
  | PropHolds p1 => interp_prop p1 bvar_interp fvar_interp f_interp

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

structure CheckContext M [Monad M] where
  visitTm : forall l r d m, Owl.opaqueSyntax -> ty l r d m -> M Unit
  log : String -> M Unit
  fresh : M Lean.Name
  curSyntax : Option Owl.opaqueSyntax

inductive CheckOutput where
  | true : CheckOutput
  | sc : SideConditionWithContext -> CheckOutput
  | and : CheckOutput -> CheckOutput -> CheckOutput
  | or : CheckOutput -> CheckOutput -> CheckOutput
  deriving ToExpr

infixr:60 " ∧sc " => CheckOutput.and
infixr:60 " ∨sc " => CheckOutput.or
notation " ⊤ " => CheckOutput.true



@[simp]
def CheckOutput.simpl (c : CheckOutput) : CheckOutput :=
  match c with
  | .true => .true
  | .and e1 e2 =>
      let e1' := e1.simpl
      let e2' := e2.simpl
      match e1', e2' with
      | .true, _ => e2'
      | _, .true => e1'
      | _, _ => e1' ∧sc e2'
  | .or e1 e2 =>
      let e1' := e1.simpl
      let e2' := e2.simpl
      match e1', e2' with
      | .true, _ => .true
      | _, .true => .true
      | _, _ => e1' ∨sc e2'
  | .sc s => .sc s



abbrev CheckContext.init [Monad M] (visit : forall l d r m, Owl.opaqueSyntax -> ty l d r m -> M Unit) (log : String -> M Unit) (fresh : M Lean.Name) : CheckContext M :=
  { visitTm := visit, curSyntax := .none, log := log, fresh := fresh }

abbrev CheckT m [Monad m] α :=
  ReaderT (CheckContext m) m (Result (Option opaqueSyntax × String) (α × CheckOutput))

-- CheckState m -> m (Result (Option opaqueSyntax × String) (α × CheckState m))

@[always_inline, simp]
instance [Monad m] : Monad (CheckT m) where
  pure := fun x => fun _ => pure (.ok (x, .true))
  bind := fun c k => fun ctx => do
    match <- (c ctx) with
    | .err e => pure (.err e)
    | .ok (x, o1) => do
        match <- (k x ctx) with
        | .err e2 => pure (.err e2)
        | .ok (res, o2) => pure $ .ok (res, o1.and o2)


def emit [Monad m] r (theta : RCtx r) (p : SideCondition r) : CheckT m Unit := fun _ =>
  pure $ .ok ((), .sc $ ⟨r, theta, p⟩)

def withSyntax [Monad m] (s : Owl.opaqueSyntax) (k : CheckT m α) : CheckT m α :=
  fun st => k {st with curSyntax := .some s}


def throw [Monad m] (s : String) : CheckT m α := fun st => pure $ .err (st.curSyntax, s)

def visit [Monad m] (s : Owl.opaqueSyntax) (t : ty l d r n) : CheckT m Unit := fun st => do
  st.visitTm _ _ _ _ s t
  pure (.ok ((), .true))

def log [Monad m] (s : String) : CheckT m Unit := fun st => do
  st.log s
  pure (.ok ((), .true))

def freshName [Monad m] : CheckT m Lean.Name := fun st => do
  let i <- st.fresh
  pure (.ok (i, .true))

def CheckT.or [Monad m] (c1 : CheckT m Unit) (c2 : CheckT m Unit) : CheckT m Unit :=
  fun ctx => do
    match <- c1 ctx with
    | .err s => return .err s
    | .ok (_, o1) => do
      match <- c2 ctx with
      | .err s => return .err s
      | .ok (_, o2) => return .ok ((), o1.or o2)


abbrev subtype_fuel := 10

-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!


def lift_RCtx_r (r : RCtx n) : RCtx (n + 1) :=
  r.map (ren_prop shift id)


partial def extract_refinements [Monad m] (t : ty l r d 0) : CheckT m (RCtx r × ty l r d 0) :=
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




def check_subtype  [Monad m] (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d )
                           (Theta : RCtx r)
                           (t1 : ty l r d 0) (t2 : ty l r d 0) : CheckT m Unit := do
    -- log s!"check subtype: {t1} <= {t2}"
    if t1 == t2 then pure () else
    match fuel with
    | 0 => throw "check_subtype: out of fuel"
    | (n + 1) =>
      match t1, t2 with
      | _, .Any => pure ()
      | .Unit, .Unit => pure ()
      | _, .refined t p => do
        check_subtype n Phi Psi Delta Theta t1 t
        emit r Theta (.PropHolds p)
      | _, .inter t21 t22 => do
        check_subtype n Phi Psi Delta Theta t1 t21
        check_subtype n Phi Psi Delta Theta t1 t22
      | _, .union t21 t22 => do
        CheckT.or (check_subtype n Phi Psi Delta Theta t1 t21)
                  (check_subtype n Phi Psi Delta Theta t1 t22)
      | .inter t11 t12, _ =>
        CheckT.or (check_subtype n Phi Psi Delta Theta t11 t2)
                  (check_subtype n Phi Psi Delta Theta t12 t2)
      | .RData l1 _, .Data l2 =>
        emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
      | .RData l1 re1, .RData l2 re2 => do
        emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
        emit r Theta (.RexpEq re1 re2)
        pure ()
      | .Data l1, .Public => do
        emit r Theta (.PhiPsiEntailCorr s!"Data {l1}, Public" (vec.from_fn Phi) Psi l1)
      | .RData l1 _, .Public => do
        emit r Theta (.PhiPsiEntailCorr s!"RData {l1}, Public" (vec.from_fn Phi) Psi l1)
        pure ()
      | .Data l1, ty.ex_r (.RData l2 (.var 0)) =>
        emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
      | .var_ty x1, .var_ty x2 =>
        emit r Theta (.TyVarEq x1 x2)
      | .Public, .Public => pure ()
      | .var_ty x, t' => check_subtype n Phi Psi Delta Theta (Delta x) t'
      | t, .var_ty x => check_subtype n Phi Psi Delta Theta t (Delta x)
      -- | .Public, .Data _ => pure ()
      | (.arr t1 t2), (.arr t1' t2') => do
        check_subtype n Phi Psi Delta Theta t1' t1
        check_subtype n Phi Psi Delta Theta t2 t2'
      | (.prod t1 t2), (.prod t1' t2') => do
        check_subtype n Phi Psi Delta Theta t1 t1'
        check_subtype n Phi Psi Delta Theta t2 t2'
      | (.sum t1 t2), (.sum t1' t2') => do
        check_subtype n Phi Psi Delta Theta t1 t1'
        check_subtype n Phi Psi Delta Theta t2 t2'
      | .Ref u, .Ref v =>
        emit r Theta (.TyEq u v)
      | .all t0 t, .all t0' t' => do
        check_subtype n Phi Psi Delta Theta t0 t0'
        let extended_delta := lift_delta (cons t0' Delta)
        check_subtype n Phi Psi extended_delta Theta t t'
      | .ex t0 t, .ex t0' t' => do
        check_subtype n Phi Psi Delta Theta t0 t0'
        let extended_delta := lift_delta (cons t0 Delta)
        check_subtype n Phi Psi extended_delta Theta t t'
      | .all_l cs lab t, .all_l cs' lab' t' => do
        let extended_phi := lift_phi (cons (cs, lab) Phi)
        let constraint := (.condition cs (.var_label "_" var_zero) (ren_label shift lab'))
        -- let constraint_holds := extended_phi |= constraint
        emit r Theta (.PhiEntails (vec.from_fn extended_phi) constraint)
        let extended_psi := lift_psi Psi
        let extended_delta := lift_delta_l Delta
        check_subtype n extended_phi extended_psi extended_delta Theta t t'
        emit r Theta (.CondSymEq cs cs')
      | .t_if lab t1 t2, t' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta Theta t1 t'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta Theta t2 t'
      | t, .t_if lab t1' t2' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta Theta t t1'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta Theta t t2'
      | _, _ =>
        let s := s!"Could not prove {repr t1} <: {repr t2}"
        emit r Theta (.PsiContextInconsistent s (vec.from_fn Phi) Psi)
        -- throw s!"check_subtype: cannot prove {t1.pretty} <= {t2.pretty}}"


@[simp]
def from_synth [Monad m] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (Theta : RCtx r)
          (t : ty l r d 0) (exp : Option (ty l r d 0)) :
          CheckT m (ty l r d 0) :=
    match exp with
    | .none => pure t
    | .some t' => do
      check_subtype subtype_fuel Phi Psi Delta Theta t t'
      pure t'


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

def infer_op [Monad M] (Theta : RCtx r) (Phi : phi_context l) (op : String) (t1 : ty l r d 0) (t2 : ty l r d 0) : CheckT M (ty l r d 0) :=
  match t1, t2 with
  | .RData l1 r1, .RData l2 r2 => do
      emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition .leq l2 l1))
      return (.RData l1 (.op op r1 r2))
  | .Public, .Public => return .Public
  | _, _ => do
    let getLabel (t : ty l r d 0) : CheckT M (label l) :=
      match t with
      | .Public => return .latl L.bot
      | .RData l _ => return l
      | .Data l => return l
      | _ => throw "infer_op: argument must be of type Data / RData / Public"
    let l1 <- getLabel t1
    let l2 <- getLabel t2
    return (.Data (label.ljoin l1 l2))

def resolve_ty [Monad M] (Gamma : gamma_context l r d n) (t : ty l r d n) : CheckT M (ty l r d 0) :=
  t.resolve_tm fun i =>
    match (Gamma i) with
    | ty.RData _ a => return a
    | _ => throw s!"Refinement expression or prop cannot make reference to non-refinfed variable"

def resolve_re [Monad M] (Gamma : gamma_context l r d n) (t : rexp r n) : CheckT M (rexp r 0) :=
  t.resolve_tm fun i =>
    match (Gamma i) with
    | ty.RData _ a => return a
    | _ => throw s!"Refinement expression or prop cannot make reference to non-refinfed variable"


mutual
def infer [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (Theta : RCtx r)
          (Gamma : gamma_context l r d m) (e : tm l r d m) (exp : Option (ty l r  d 0)) :
          CheckT M (ty l r  d 0) :=
      match e with
      | .mk stx v => do
        let t <- withSyntax stx $ inferX Phi Psi Delta Theta Gamma v exp
        let t := t.simplify Psi
        visit stx t
        return t

def inferX [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (Theta : RCtx r)
          (Gamma : gamma_context l r d m) (e : tmX l r d m) (exp : Option (ty l r  d 0)) :
          CheckT M (ty l r  d 0) :=
  match e with
  | .var_tm x =>
      -- TODO: flatten
      from_synth Phi Psi Delta Theta (Gamma x) exp
  | .skip =>
      from_synth Phi Psi Delta Theta .Unit exp
  | .bitstring b =>
      from_synth Phi Psi Delta Theta (.RData (.latl L.bot) (.const b)) exp
  | .Op op e1 e2 => do-- This case is long! Might need a step by step.
      let t1 <- infer Phi Psi Delta Theta Gamma e1 .none
      let t2 <- infer Phi Psi Delta Theta Gamma e2 .none
      let tres <- infer_op Theta Phi op t1 t2
      from_synth Phi Psi Delta Theta tres exp
  | .zero e => do
      let t <- infer Phi Psi Delta Theta Gamma e none
      match t with
      | .Public | .Data _ | .RData _ _ =>
        from_synth Phi Psi Delta Theta .Public exp
      | _ => throw "zero: not bitstring"
  | .if_tm e e1 e2 => do
    let _ <- infer Phi Psi Delta Theta Gamma e (.some .Public)
    let t1 <- infer Phi Psi Delta Theta Gamma e1 exp
    let t2 <- infer Phi Psi Delta Theta Gamma e2 exp
    check_subtype subtype_fuel Phi Psi Delta Theta t2 t1
    from_synth Phi Psi Delta Theta t1 exp
  | .tlet e1 e2 => do
    let t1 <- infer Phi Psi Delta Theta Gamma e1 .none
    let (theta', t1') <- extract_refinements t1
    infer Phi Psi Delta (Theta ++ theta') (cons t1' Gamma) e2 exp
  | .union_elim e1 e2 => do
    let t1 <- infer Phi Psi Delta Theta Gamma e1 .none
    match t1 with
    | .union t11 t12 => do
        let res1 <- infer Phi Psi Delta Theta (cons t11 Gamma) e2 exp
        let res2 <- infer Phi Psi Delta Theta (cons t12 Gamma) e2 exp
        if res1 == res2 then return res1
                        else throw "union_elim: must get same type on both sides"
    | _ => infer Phi Psi Delta Theta (cons t1 Gamma) e2 exp
  | .alloc e => do
    let t <- infer Phi Psi Delta Theta Gamma e .none
    from_synth Phi Psi Delta Theta (.Ref t) exp
  | .dealloc e => do
    let t <- infer Phi Psi Delta Theta Gamma e .none
    match t with
    | .Ref t0 => from_synth Phi Psi Delta Theta t0 exp
    | _ => throw "dealloc"
  | .assign e1 e2 => do
    let t0 <- infer Phi Psi Delta Theta Gamma e1 .none
    match t0 with
    | .Ref t1 => do
      let _ <- infer Phi Psi Delta Theta Gamma e2 (.some t1)
      from_synth Phi Psi Delta Theta .Unit exp
    | _ => throw "assign"
  | .inl e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Theta Gamma e (.some t1)
       pure (.sum t1 t2)
    | _ => throw "inl"
  | .inr e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Theta Gamma e (.some t2)
       pure (.sum t1 t2)
    | _ => throw "inr"
  | .fixlam _ e =>
    match exp with
    | .some (.arr t t') => do
       let extended_gamma := cons (.arr t t') (cons t Gamma)
       let _ <- infer Phi Psi Delta Theta extended_gamma e (.some t')
       pure (.arr t t')
    | _ => throw "fixlam"
  | .app e1 e2 =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Theta Gamma e1 .none with
      | .arr t t' => do
        let _ <- infer Phi Psi Delta Theta Gamma e2 (.some t)
        pure t'
      | t => throw s!"app: got unexpected type for function: {t} "
    | .some expected => do
      let t1 <- infer Phi Psi Delta Theta Gamma e2 .none
      let _ <- infer Phi Psi Delta Theta Gamma e1 (.some (.arr t1 expected))
      pure expected
  | .tm_pair e1 e2 => do
    let t1 <- infer Phi Psi Delta Theta Gamma e1 .none
    let t2 <- infer Phi Psi Delta Theta Gamma e2 .none
    from_synth Phi Psi Delta Theta (.prod t1 t2) exp
  | .left_tm e => do
    match <- infer Phi Psi Delta Theta Gamma e .none with
    | .prod t1 _ => from_synth Phi Psi Delta Theta t1 exp
    | _ => throw "left_tm"
  | .right_tm e => do
    match <- infer Phi Psi Delta Theta Gamma e .none with
    | .prod _ t2 => from_synth Phi Psi Delta Theta t2 exp
    | _ => throw "right_tm"
  | .case e e1 e2 => do
    match <- infer Phi Psi Delta Theta Gamma e .none with
    | .sum t1 t2 => do
      let r1 <- infer Phi Psi Delta Theta (cons t1 Gamma) e1 exp
      let r2 <- infer Phi Psi Delta Theta (cons t2 Gamma) e2 exp
      match exp with
      | .some res => return res
      | none => do
        check_subtype subtype_fuel Phi Psi Delta Theta r2 r1
        pure r1
    | _ => throw "case"
  | .rlam e =>
    match exp with
    | .some (.all_r t0) => do
        let _ <- infer Phi Psi (lift_delta_r Delta) (lift_RCtx_r Theta) (lift_gamma_r Gamma) e (.some t0)
        pure (.all_r t0)
    | _ => throw "Error when type checking Λr: expected type must be of the form ∀ x. τ"
  | .tlam e =>
    match exp with
    | .some (.all t0 t) => do
      let _ <- infer Phi Psi (lift_delta (cons t0 Delta)) Theta (lift_gamma_d Gamma) e (.some t)
      pure (.all t0 t)
    | _ => throw s!"Error when type checking Λ: expected type must be a ∀. Instead, got {exp} "
  | .rapp e re => do
    let re' <- resolve_re Gamma re
    match <- infer Phi Psi Delta Theta Gamma e .none with
    | .all_r t0 => do
      let result_ty := subst_ty (.var_label "_") (cons re' .var) .var_ty t0;
      from_synth Phi Psi Delta Theta result_ty exp
    | _ => throw "rapp: expected type must be of the form ∀r x. τ"
  | .tapp e t' => do
    let t'' <- resolve_ty Gamma t'
    match <- infer Phi Psi Delta Theta Gamma e .none with
    | .all t0 t => do
      check_subtype subtype_fuel Phi Psi Delta Theta t'' t0
      let result_ty := subst_ty (.var_label "_") .var (cons t'' .var_ty) t;
      from_synth Phi Psi Delta Theta result_ty exp
    | _ => throw "tapp"
  | .rpack re e => do
    let re' <- resolve_re Gamma re
    match exp with
     | .some (.ex_r t0) => do
      let substituted_type := subst_ty (.var_label "_") (cons re' .var) .var_ty t0
      let _ <- infer Phi Psi Delta Theta Gamma e (.some substituted_type)
      pure (.ex_r t0)
     | _ => throw "rpack: need expected type of form rpack(r, e)"
  | .pack t' e => do
    let t' <- resolve_ty Gamma t'
    match exp with
    | .none => throw "pack: empty expected"
    | .some (.ex t0 t) => do
      let substituted_type := subst_ty (.var_label "_") .var (cons t' .var_ty) t
      check_subtype subtype_fuel Phi Psi Delta Theta t' t0
      let _ <- infer Phi Psi Delta Theta Gamma e (.some substituted_type)
      pure (.ex t0 t)
    | _ => throw "pack"
  | .unpack e e' =>
    match exp with
    | .none => throw "unpack: empty expected"
    | .some exp_ty => do
      match <- infer Phi Psi Delta Theta Gamma e .none with
      | .ex t0 t => do
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id id shift id exp_ty
        let _ <- infer Phi Psi extended_delta Theta extended_gamma e' (.some renamed_t')
        pure exp_ty
      | _ => throw "unpack"
  | .l_lam e =>
    match exp with
    | .none => throw "l_lam: empty expected"
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body => do
        let _ <- infer (lift_phi ((cons (cs, lab)) Phi))
                  (lift_psi Psi)
                  (lift_delta_l Delta) Theta (lift_gamma_l Gamma)
                  e (.some t_body)
        pure exp_ty
      | _ => throw "l_lam"
  | .lapp e lab' =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Theta Gamma e .none with
      | .all_l cs lab t  => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition cs lab lab'))
        pure result_ty
      | _ => throw "lapp"
    | .some exp_ty => do
      match <- infer Phi Psi Delta Theta Gamma e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        check_subtype subtype_fuel Phi Psi Delta Theta result_ty exp_ty
        emit r Theta (.PhiEntails (vec.from_fn Phi) (.condition cs lab lab'))
        pure exp_ty
      | _ => throw "lapp"
  | .annot e t' => do
    let t' <- resolve_ty Gamma t'
    let r <- infer Phi Psi Delta Theta Gamma e (.some t')
    from_synth Phi Psi Delta Theta r exp
  | .if_c lab e1 e2 => do
    let t1 <- infer Phi ((.corr lab) :: Psi) Delta Theta Gamma e1 none
    let t2 <- infer Phi ((.not_corr lab) :: Psi) Delta Theta Gamma e2 none
    from_synth Phi Psi Delta Theta (.t_if lab t1 t2) exp
  | .corr_case lab e =>
    match exp with
    | .none => do
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      let t1 <- infer Phi psi_corr Delta Theta Gamma e .none
      let t2 <- infer Phi psi_not_corr Delta Theta Gamma e .none
      pure (.t_if lab t1 t2)
    | .some exp_ty =>do
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      let _ <- infer Phi psi_corr Delta Theta Gamma e (.some exp_ty)
      let _ <- infer Phi psi_not_corr Delta Theta Gamma e (.some exp_ty)
      pure exp_ty
  | .sync e => do
    let _ <- infer Phi Psi Delta Theta Gamma e (.some .Public)
    from_synth Phi Psi Delta Theta .Public exp
  | .default => throw "infer: unhandled case"
  | .loc _ => throw "infer: unhandled case"
  | .error => throw "infer: unhandled case"
end

opaque TypeError (o : Option opaqueSyntax) (s : String) : Prop := False

open PrettyPrinter Delaborator

@[app_unexpander TypeError]
def delabTypeError : Unexpander
  | `($_typeerror $_o $s) => set_option hygiene false in `(type error $s)
  | _ => set_option hygiene false in `(bad)


-- def has_type_infer M [Monad M] (visit : forall l r d, Owl.opaqueSyntax -> ty l r d -> M Unit)
--    (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
--     (Gamma : gamma_context l r d m) (e : tm l r d m) (exp : ty l r d) : M (Result Prop (List SideCondition)) := do
--   match <- (infer Phi Psi Delta Gamma e (.some exp)) (CheckState.init visit (fun _ => pure ())) with
--   | .ok (_, p) => pure $ .ok $ p.side_condition
--   | .err e => pure $ .err $ TypeError e.1 e.2

-- Useful TODO
/-
theorem infer_sound Phi Psi Delta Gamma (e : tm l d m) (exp : ty l d) :
  has_type_infer Id (fun _ _ _ _ => ()) Phi Psi Delta Gamma e exp ->
  has_type Phi Psi Delta Gamma e exp := by
    sorry
-/

end OwlTc
