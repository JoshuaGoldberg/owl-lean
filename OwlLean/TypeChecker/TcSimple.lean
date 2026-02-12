import OwlLean.TypeChecker.OwlTyping
import OwlLean.OwlLang.ToString

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic

@[simp]
def Owl.ty.simplify (t : ty l r d ) (corrs : List (corruption l)): ty l r d  :=
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





inductive SideCondition where
  | PhiEntails : phi_context_repr l -> Owl.constr l -> SideCondition
  | PhiPsiEntailCorr : String -> phi_context_repr l -> psi_context l -> label l -> SideCondition
  | TyVarEq : Fin d -> Fin d -> SideCondition
  | TyEq : ty l d r -> ty l d r -> SideCondition
  | CondSymEq : cond_sym -> cond_sym -> SideCondition
  | PsiContextInconsistent : String -> phi_context_repr l -> psi_context l -> SideCondition
  | RexpEq : rexp r -> rexp r -> SideCondition
deriving ToExpr

instance : ToString SideCondition where
  toString := fun _ => "<sc>"


def rexp_interp (re : rexp r) (f : String -> String -> String -> String ) (m : Fin r -> String) :=
  match re with
  | .var i => m i
  | .op s r1 r2 => f s (rexp_interp r1 f m) (rexp_interp r2 f m)
  | .const b => b



-- TODO: ToString for SideCondition.

@[simp]
def SideCondition.interp (p : SideCondition) : Prop :=
  match p with
  | PhiEntails phi c => vec.to_fn phi |= c
  | PhiPsiEntailCorr _ phi psi l => phi_psi_entail_corr (vec.to_fn phi) psi (.corr l)
  | TyVarEq x y => x = y
  | TyEq t1 t2 => t1 = t2
  | CondSymEq c1 c2 => c1 = c2
  | PsiContextInconsistent _ phi psi => psi_context_inconsistent (vec.to_fn phi) psi
  | RexpEq re1 re2 => (forall f m, rexp_interp re1 f m = rexp_interp re2 f m)

inductive Result ε α where
  | ok : α -> Result ε α
  | err : ε -> Result ε α


structure CheckState M [Monad M] where
  visitTm : forall l r d , Owl.opaqueSyntax -> ty l r d -> M Unit
  log : String -> M Unit
  curSyntax : Option Owl.opaqueSyntax
  side_condition : List SideCondition

abbrev CheckState.init [Monad M] (visit : forall l d r, Owl.opaqueSyntax -> ty l d r -> M Unit) (log : String -> M Unit) : CheckState M :=
  { visitTm := visit, curSyntax := .none, side_condition := [], log := log }

abbrev CheckT m [Monad m] α := CheckState m -> m (Result (Option opaqueSyntax × String) (α × CheckState m))

@[always_inline, simp]
instance [Monad m] : Monad (CheckT m) where
  pure := fun x => fun p => pure (.ok (x, p))
  bind := fun c k => fun p => do
    match <- (c p) with
    | .err e => pure (.err e)
    | .ok (x, p') => k x p'

def emit [Monad m] (p : SideCondition) : CheckT m Unit := fun st => pure $ .ok ((),
  {st with side_condition := p :: st.side_condition })

def withSyntax [Monad m] (s : Owl.opaqueSyntax) (k : CheckT m α) : CheckT m α :=
  fun st => k {st with curSyntax := .some s}


def throw [Monad m] (s : String) : CheckT m α := fun st => pure $ .err (st.curSyntax, s)

def visit [Monad m] (s : Owl.opaqueSyntax) (t : ty l d r) : CheckT m Unit := fun st => do
  st.visitTm _ _ _ s t
  pure (.ok ((), st))

def log [Monad m] (s : String) : CheckT m Unit := fun st => do
  st.log s
  pure (.ok ((), st))


abbrev subtype_fuel := 10

-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!



def check_subtype  [Monad m] (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d )
                           (t1 : ty l r d ) (t2 : ty l r d) : CheckT m Unit := do
    log s!"check subtype: {t1} <= {t2}"
    if t1 == t2 then pure () else
    match fuel with
    | 0 => throw "check_subtype: out of fuel"
    | (n + 1) =>
      match t1, t2 with
      | _, .Any => pure ()
      | .Unit, .Unit => pure ()
      | .RData l1 _, .Data l2 =>
        emit (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
      | .RData l1 re1, .RData l2 re2 => do
        emit (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
        emit (.RexpEq re1 re2)
        pure ()
      | .Data l1, .Public => do
        emit (.PhiPsiEntailCorr s!"Data {l1}, Public" (vec.from_fn Phi) Psi l1)
      | .RData l1 _, .Public => do
        emit (.PhiPsiEntailCorr s!"RData {l1}, Public" (vec.from_fn Phi) Psi l1)
        pure ()
      | .var_ty x1, .var_ty x2 =>
        emit (.TyVarEq x1 x2)
      | .Public, .Public => pure ()
      | .var_ty x, t' => check_subtype n Phi Psi Delta (Delta x) t'
      | t, .var_ty x => check_subtype n Phi Psi Delta t (Delta x)
      -- | .Public, .Data _ => pure ()
      | (.arr t1 t2), (.arr t1' t2') => do
        check_subtype n Phi Psi Delta t1' t1
        check_subtype n Phi Psi Delta t2 t2'
      | (.prod t1 t2), (.prod t1' t2') => do
        check_subtype n Phi Psi Delta t1 t1'
        check_subtype n Phi Psi Delta t2 t2'
      | (.sum t1 t2), (.sum t1' t2') => do
        check_subtype n Phi Psi Delta t1 t1'
        check_subtype n Phi Psi Delta t2 t2'
      | .Ref u, .Ref v =>
        emit (.TyEq u v)
      | .all t0 t, .all t0' t' => do
        check_subtype n Phi Psi Delta t0 t0'
        let extended_delta := lift_delta (cons t0' Delta)
        check_subtype n Phi Psi extended_delta t t'
      | .ex t0 t, .ex t0' t' => do
        check_subtype n Phi Psi Delta t0 t0'
        let extended_delta := lift_delta (cons t0 Delta)
        check_subtype n Phi Psi extended_delta t t'
      | .all_l cs lab t, .all_l cs' lab' t' => do
        let extended_phi := lift_phi (cons (cs, lab) Phi)
        let constraint := (.condition cs (.var_label "_" var_zero) (ren_label shift lab'))
        -- let constraint_holds := extended_phi |= constraint
        emit (.PhiEntails (vec.from_fn extended_phi) constraint)
        let extended_psi := lift_psi Psi
        let extended_delta := lift_delta_l Delta
        check_subtype n extended_phi extended_psi extended_delta t t'
        emit (.CondSymEq cs cs')
      | .t_if lab t1 t2, t' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta t1 t'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta t2 t'
      | t, .t_if lab t1' t2' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta t t1'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta t t2'
      | _, _ =>
        let s := s!"Could not prove {repr t1} <: {repr t2}"
        emit (.PsiContextInconsistent s (vec.from_fn Phi) Psi)
        -- throw s!"check_subtype: cannot prove {t1.pretty} <= {t2.pretty}}"


@[simp]
def from_synth [Monad m] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (t : ty l r d) (exp : Option (ty l r d)) :
          CheckT m (ty l r d) :=
    match exp with
    | .none => pure t
    | .some t' => do
      check_subtype subtype_fuel Phi Psi Delta t t'
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

def infer_op [Monad M] (Phi : phi_context l) (op : String) (t1 : ty l r d) (t2 : ty l r d) : CheckT M (ty l r d) :=
  match t1, t2 with
  | .RData l1 r1, .RData l2 r2 => do
      emit (.PhiEntails (vec.from_fn Phi) (.condition .leq l2 l1))
      return (.RData l1 (.op op r1 r2))
  | .Public, .Public => return .Public
  | _, _ => do
    let getLabel (t : ty l r d) : CheckT M (label l) :=
      match t with
      | .Public => return .latl L.bot
      | .RData l _ => return l
      | .Data l => return l
      | _ => throw "infer_op: argument must be of type Data / RData / Public"
    let l1 <- getLabel t1
    let l2 <- getLabel t2
    return (.Data (label.ljoin l1 l2))


mutual
def infer [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (Gamma : gamma_context l r d m) (e : tm l r d m) (exp : Option (ty l r  d)) :
          CheckT M (ty l r  d) :=
      match e with
      | .mk stx v => do
        let t <- withSyntax stx $ inferX Phi Psi Delta Gamma v exp
        let t := t.simplify Psi
        visit stx t
        return t

def inferX [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
          (Gamma : gamma_context l r d m) (e : tmX l r d m) (exp : Option (ty l r  d)) :
          CheckT M (ty l r  d) :=
  match e with
  | .var_tm x =>
      from_synth Phi Psi Delta (Gamma x) exp
  | .skip =>
      from_synth Phi Psi Delta .Unit exp
  | .bitstring b =>
      from_synth Phi Psi Delta (.RData (.latl L.bot) (.const b)) exp
  | .Op op e1 e2 => do-- This case is long! Might need a step by step.
      let t1 <- infer Phi Psi Delta Gamma e1 .none
      let t2 <- infer Phi Psi Delta Gamma e2 .none
      let tres <- infer_op Phi op t1 t2
      from_synth Phi Psi Delta tres exp
  | .zero e => do
      let t <- infer Phi Psi Delta Gamma e none
      match t with
      | .Public | .Data _ | .RData _ _ =>
        from_synth Phi Psi Delta .Public exp
      | _ => throw "zero: not bitstring"
  | .if_tm e e1 e2 => do
    let _ <- infer Phi Psi Delta Gamma e (.some .Public)
    let t1 <- infer Phi Psi Delta Gamma e1 exp
    let t2 <- infer Phi Psi Delta Gamma e2 exp
    check_subtype subtype_fuel Phi Psi Delta t2 t1
    from_synth Phi Psi Delta t1 exp
  | .letr e1 e2 => do
    let t1 <- infer Phi Psi Delta Gamma e1 .none
    match t1 with
    | .ex_r t0 =>
      let res <- infer Phi Psi (lift_delta_r Delta) (cons t0 (lift_gamma_r Gamma)) e2 (exp.map (ren_ty id shift id))
      if h0 : res.r_free 0 then
        return res.down 0 h0
      else
        throw "letr: result type would let refinement escape context"
    | _ =>
      let res <- infer Phi Psi (lift_delta_r Delta) (cons (ren_ty id shift id t1) (lift_gamma_r Gamma)) e2 (exp.map (ren_ty id shift id))
      if h0 : res.r_free 0 then
        return res.down 0 h0
      else
        throw "letr: result type would let refinement escape context"
  | .alloc e => do
    let t <- infer Phi Psi Delta Gamma e .none
    from_synth Phi Psi Delta (.Ref t) exp
  | .dealloc e => do
    let t <- infer Phi Psi Delta Gamma e .none
    match t with
    | .Ref t0 => from_synth Phi Psi Delta t0 exp
    | _ => throw "dealloc"
  | .assign e1 e2 => do
    let t0 <- infer Phi Psi Delta Gamma e1 .none
    match t0 with
    | .Ref t1 => do
      let _ <- infer Phi Psi Delta Gamma e2 (.some t1)
      from_synth Phi Psi Delta .Unit exp
    | _ => throw "assign"
  | .inl e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Gamma e (.some t1)
       pure (.sum t1 t2)
    | _ => throw "inl"
  | .inr e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Gamma e (.some t2)
       pure (.sum t1 t2)
    | _ => throw "inr"
  | .fixlam _ e =>
    match exp with
    | .some (.arr t t') => do
       let extended_gamma := cons (.arr t t') (cons t Gamma)
       let _ <- infer Phi Psi Delta extended_gamma e (.some t')
       pure (.arr t t')
    | _ => throw "fixlam"
  | .app e1 e2 =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Gamma e1 .none with
      | .arr t t' => do
        let _ <- infer Phi Psi Delta Gamma e2 (.some t)
        pure t'
      | t => throw s!"app: got unexpected type for function: {t} "
    | .some expected => do
      let t1 <- infer Phi Psi Delta Gamma e2 .none
      let _ <- infer Phi Psi Delta Gamma e1 (.some (.arr t1 expected))
      pure expected
  | .tm_pair e1 e2 => do
    let t1 <- infer Phi Psi Delta Gamma e1 .none
    let t2 <- infer Phi Psi Delta Gamma e2 .none
    from_synth Phi Psi Delta (.prod t1 t2) exp
  | .left_tm e => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .prod t1 _ => from_synth Phi Psi Delta t1 exp
    | _ => throw "left_tm"
  | .right_tm e => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .prod _ t2 => from_synth Phi Psi Delta t2 exp
    | _ => throw "right_tm"
  | .case e e1 e2 => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .sum t1 t2 => do
      let r1 <- infer Phi Psi Delta (cons t1 Gamma) e1 exp
      let r2 <- infer Phi Psi Delta (cons t2 Gamma) e2 exp
      match exp with
      | .some res => return res
      | none => do
        check_subtype subtype_fuel Phi Psi Delta r2 r1
        pure r1
    | _ => throw "case"
  | .rlam e =>
    match exp with
    | .some (.all_r t0) => do
        let _ <- infer Phi Psi (lift_delta_r Delta) (lift_gamma_r Gamma) e (.some t0)
        pure (.all_r t0)
    | _ => throw "Error when type checking Λr: expected type must be of the form ∀ x. τ"
  | .tlam e =>
    match exp with
    | .some (.all t0 t) => do
      let _ <- infer Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t)
      pure (.all t0 t)
    | _ => throw s!"Error when type checking Λ: expected type must be a ∀. Instead, got {exp} "
  | .rapp e re => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .all_r t0 => do
      let result_ty := subst_ty (.var_label "_") (cons re .var) .var_ty t0;
      from_synth Phi Psi Delta result_ty exp
    | _ => throw "rapp: expected type must be of the form ∀r x. τ"
  | .tapp e t' => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .all t0 t => do
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let result_ty := subst_ty (.var_label "_") .var (cons t' .var_ty) t;
      from_synth Phi Psi Delta result_ty exp
    | _ => throw "tapp"
  | .rpack re e =>
    match exp with
     | .some (.ex_r t0) => do
      let substituted_type := subst_ty (.var_label "_") (cons re .var) .var_ty t0
      let _ <- infer Phi Psi Delta Gamma e (.some substituted_type)
      pure (.ex_r t0)
     | _ => throw "rpack: need expected type of form rpack(r, e)"
  | .pack t' e =>
    match exp with
    | .none => throw "pack: empty expected"
    | .some (.ex t0 t) => do
      let substituted_type := subst_ty (.var_label "_") .var (cons t' .var_ty) t
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let _ <- infer Phi Psi Delta Gamma e (.some substituted_type)
      pure (.ex t0 t)
    | _ => throw "pack"
  | .unpack e e' =>
    match exp with
    | .none => throw "unpack: empty expected"
    | .some exp_ty => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .ex t0 t => do
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id id shift exp_ty
        let _ <- infer Phi Psi extended_delta extended_gamma e' (.some renamed_t')
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
                  (lift_delta_l Delta) (lift_gamma_l Gamma)
                  e (.some t_body)
        pure exp_ty
      | _ => throw "l_lam"
  | .lapp e lab' =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .all_l cs lab t  => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        emit (.PhiEntails (vec.from_fn Phi) (.condition cs lab lab'))
        pure result_ty
      | _ => throw "lapp"
    | .some exp_ty => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' (.var_label "_")) .var .var_ty t
        check_subtype subtype_fuel Phi Psi Delta result_ty exp_ty
        emit (.PhiEntails (vec.from_fn Phi) (.condition cs lab lab'))
        pure exp_ty
      | _ => throw "lapp"
  | .annot e t' => do -- LONG CASE TO HANDLE IF CHECKING PROPERLY
    let r <- infer Phi Psi Delta Gamma e (.some t')
    from_synth Phi Psi Delta r exp
  | .if_c lab e1 e2 => do
    let t1 <- infer Phi ((.corr lab) :: Psi) Delta Gamma e1 none
    let t2 <- infer Phi ((.not_corr lab) :: Psi) Delta Gamma e2 none
    from_synth Phi Psi Delta (.t_if lab t1 t2) exp
  | .corr_case lab e =>
    match exp with
    | .none => do
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      let t1 <- infer Phi psi_corr Delta Gamma e .none
      let t2 <- infer Phi psi_not_corr Delta Gamma e .none
      pure (.t_if lab t1 t2)
    | .some exp_ty =>do
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      let _ <- infer Phi psi_corr Delta Gamma e (.some exp_ty)
      let _ <- infer Phi psi_not_corr Delta Gamma e (.some exp_ty)
      pure exp_ty
  | .sync e => do
    let _ <- infer Phi Psi Delta Gamma e (.some .Public)
    from_synth Phi Psi Delta .Public exp
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


def has_type_infer M [Monad M] (visit : forall l r d, Owl.opaqueSyntax -> ty l r d -> M Unit)
   (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l r d)
    (Gamma : gamma_context l r d m) (e : tm l r d m) (exp : ty l r d) : M (Result Prop (List SideCondition)) := do
  match <- (infer Phi Psi Delta Gamma e (.some exp)) (CheckState.init visit (fun _ => pure ())) with
  | .ok (_, p) => pure $ .ok $ p.side_condition
  | .err e => pure $ .err $ TypeError e.1 e.2

-- Useful TODO
/-
theorem infer_sound Phi Psi Delta Gamma (e : tm l d m) (exp : ty l d) :
  has_type_infer Id (fun _ _ _ _ => ()) Phi Psi Delta Gamma e exp ->
  has_type Phi Psi Delta Gamma e exp := by
    sorry
-/

end OwlTc
