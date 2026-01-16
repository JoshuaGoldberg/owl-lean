import OwlLean.TypeChecker.OwlTyping
import OwlLean.OwlLang.ToString

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic

@[simp]
def Owl.ty.simplify (t : ty l d) (corrs : List (corruption l)): ty l d :=
  match t with
  | .var_ty _ => t
  | .Any => t
  | .Unit => t
  | .Data _ => t
  | .Sing _ => t
  | .Public => t
  | .Ref t0 => .Ref t0
  | .arr t0 t1 => .arr (t0.simplify corrs) (t1.simplify corrs)
  | .ex t0 t1 => .ex (t0.simplify corrs) (t1.simplify corrs)
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


















namespace OwlTc





inductive SideCondition where
  | PhiEntails : phi_context_repr l -> Owl.constr l -> SideCondition
  | PhiPsiEntailCorr : phi_context_repr l -> psi_context l -> label l -> SideCondition
  | TyVarEq : Fin d -> Fin d -> SideCondition
  | TyEq : ty l d -> ty l d -> SideCondition
  | CondSymEq : cond_sym -> cond_sym -> SideCondition
  | PsiContextInconsistent : String -> phi_context_repr l -> psi_context l -> SideCondition
deriving ToExpr

instance : ToString SideCondition where
  toString := fun _ => "<sc>"



-- TODO: ToString for SideCondition.

@[simp]
def SideCondition.interp (p : SideCondition) : Prop :=
  match p with
  | PhiEntails phi c => vec.to_fn phi |= c
  | PhiPsiEntailCorr phi psi l => phi_psi_entail_corr (vec.to_fn phi) psi (.corr l)
  | TyVarEq x y => x = y
  | TyEq t1 t2 => t1 = t2
  | CondSymEq c1 c2 => c1 = c2
  | PsiContextInconsistent _ phi psi => psi_context_inconsistent (vec.to_fn phi) psi

inductive Result ε α :=
  | ok : α -> Result ε α
  | err : ε -> Result ε α


structure CheckState M [Monad M] where
  visitTm : forall l d, Owl.opaqueSyntax -> ty l d -> M Unit
  log : String -> M Unit
  curSyntax : Option Owl.opaqueSyntax
  side_condition : List SideCondition

abbrev CheckState.init [Monad M] (visit : forall l d, Owl.opaqueSyntax -> ty l d -> M Unit) (log : String -> M Unit) : CheckState M :=
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

def visit [Monad m] (s : Owl.opaqueSyntax) (t : ty l d) : CheckT m Unit := fun st => do
  st.visitTm _ _ s t
  pure (.ok ((), st))

def log [Monad m] (s : String) : CheckT m Unit := fun st => do
  st.log s
  pure (.ok ((), st))



abbrev subtype_fuel := 10

-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!

def check_subtype  [Monad m] (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : CheckT m Unit := do
    log s!"check subtype: {t1} <= {t2}"
    if t1 == t2 then pure () else
    match fuel with
    | 0 => throw "check_subtype: out of fuel"
    | (n + 1) =>
      match t1, t2 with
      | _, .Any => pure ()
      | .Unit, .Unit => pure ()
      | .Data l1, .Data l2 => do
        emit (.PhiEntails (vec.from_fn Phi) (.condition .leq l1 l2))
        pure ()
      | .Data l1, .Public => do
        emit (.PhiPsiEntailCorr (vec.from_fn Phi) Psi l1)
        pure ()
      | .var_ty x1, .var_ty x2 =>
        emit (.TyVarEq x1 x2)
      | .Public, .Public => pure ()
      | .var_ty x, t' => check_subtype n Phi Psi Delta (Delta x) t'
      | t, .var_ty x => check_subtype n Phi Psi Delta t (Delta x)
      | .Public, .Data _ => pure ()
      | .Sing _, .Public => pure ()
      | .Sing _, .Data _ => pure ()
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
        let constraint := (.condition cs (.var_label var_zero) (ren_label shift lab'))
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
        let s := s!"Could not prove {t1} <: {t2}"
        emit (.PsiContextInconsistent s (vec.from_fn Phi) Psi)
        -- throw s!"check_subtype: cannot prove {t1.pretty} <= {t2.pretty}}"


@[simp]
def from_synth [Monad m] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (t : ty l d) (exp : Option (ty l d)) :
          CheckT m (ty l d) :=
    match exp with
    | .none => pure t
    | .some t' => do
      check_subtype subtype_fuel Phi Psi Delta t t'
      pure t'

@[simp]
def to_data [Monad m] (fuel : Nat) (Delta : delta_context l d) (t : ty l d)
  : CheckT m (Owl.label l) :=
    match fuel with
    | 0 => throw "to_data: out of fuel"
    | n + 1 =>
      match t with
      | .Data l1 => pure l1
      | .Public => pure (.latl L.bot)
      | .Sing _ => pure (.latl L.bot)
      | .var_ty x => to_data n Delta (Delta x)
      | _ => throw s!"to_data: unhandled case: {t}"


-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"
-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type

mutual
def infer [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          CheckT M (ty l d) :=
      match e with
      | .mk stx v => do
        let t <- withSyntax stx $ inferX Phi Psi Delta Gamma v exp
        let t := t.simplify Psi
        visit stx t
        return t

def inferX [Monad M] (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tmX l d m) (exp : Option (ty l d)) :
          CheckT M (ty l d) :=
  match e with
  | .var_tm x =>
      from_synth Phi Psi Delta (Gamma x) exp
  | .skip =>
      from_synth Phi Psi Delta .Unit exp
  | .bitstring b =>
      from_synth Phi Psi Delta (.Sing b) exp
  | .Op op e1 e2 => do-- This case is long! Might need a step by step.
      let t1 <- infer Phi Psi Delta Gamma e1 .none
      let t2 <- infer Phi Psi Delta Gamma e2 .none
      let l1 <- to_data 10 Delta t1
      let l2 <- to_data 10 Delta t2
      emit (.PhiEntails (vec.from_fn Phi) (.condition .leq l2 l1))
      from_synth Phi Psi Delta (.Data l1) exp
  | .zero e => do
      let t1 <- infer Phi Psi Delta Gamma e .none
      let l1 <- to_data 10 Delta t1
      from_synth Phi Psi Delta .Public exp
  | .if_tm e e1 e2 => do
    let t0 <- infer Phi Psi Delta Gamma e (.some .Public)
    let t1 <- infer Phi Psi Delta Gamma e1 exp
    let t2 <- infer Phi Psi Delta Gamma e2 exp
    check_subtype subtype_fuel Phi Psi Delta t2 t1
    from_synth Phi Psi Delta t1 exp
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
    | .prod t1 t2 => from_synth Phi Psi Delta t1 exp
    | _ => throw "left_tm"
  | .right_tm e => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .prod t1 t2 => from_synth Phi Psi Delta t2 exp
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
  | .tlam e =>
    match exp with
    | .some (.all t0 t) => do
      let _ <- infer Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t)
      pure (.all t0 t)
    | _ => throw "tlam"
  | .tapp e t' => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .all t0 t => do
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let result_ty := subst_ty .var_label (cons t' .var_ty) t;
      from_synth Phi Psi Delta result_ty exp
    | _ => throw "tapp"
  | .pack t' e =>
    match exp with
    | .none => throw "pack: empty expected"
    | .some (.ex t0 t) => do
      let substituted_type := subst_ty .var_label (cons t' .var_ty) t
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let r <- infer Phi Psi Delta Gamma e (.some substituted_type)
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
        let renamed_t' := ren_ty id shift exp_ty
        let res <- infer Phi Psi extended_delta extended_gamma e' (.some renamed_t')
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
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        emit (.PhiEntails (vec.from_fn Phi) (.condition cs lab lab'))
        pure result_ty
      | _ => throw "lapp"
    | .some exp_ty => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
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
  | _ => throw "infer: unhandled case"
end

opaque TypeError (o : Option opaqueSyntax) (s : String) : Prop := False

open PrettyPrinter Delaborator

@[app_unexpander TypeError]
def delabTypeError : Unexpander
  | `($_typeerror $_o $s) => set_option hygiene false in `(type error $s)
  | _ => set_option hygiene false in `(bad)


def has_type_infer M [Monad M] (visit : forall l d, Owl.opaqueSyntax -> ty l d -> M Unit)
   (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
    (Gamma : gamma_context l d m) (e : tm l d m) (exp : ty l d) : M (Result Prop (List SideCondition)) := do
  match <- (infer Phi Psi Delta Gamma e (.some exp)) (CheckState.init visit (fun _ => pure ())) with
  | .ok (_, p) => pure $ .ok $ p.side_condition
  | .err e => pure $ .err $ TypeError e.1 e.2

/-
theorem infer_sound Phi Psi Delta Gamma (e : tm l d m) (exp : ty l d) :
  has_type_infer Id (fun _ _ _ _ => ()) Phi Psi Delta Gamma e exp ->
  has_type Phi Psi Delta Gamma e exp := by
    sorry
-/

end OwlTc
