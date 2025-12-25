import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic

namespace OwlTc


abbrev Check α := EStateM Unit Prop α

def emit (p : Prop) : Check Unit := do
  let acc <- get
  set (p ∧ acc)

abbrev subtype_fuel := 10

-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!

def check_subtype  (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : Check Unit :=
    match fuel with
    | 0 => throw ()
    | (n + 1) =>
      match t1, t2 with
      | x, .Any => pure ()
      | .Unit, .Unit => pure ()
      | .Data l1, .Data l2 => do
        emit (Phi |= (.condition .leq l1 l2))
        pure ()
      | .Data l1, .Public => do
        emit ( phi_psi_entail_corr Phi Psi (.corr l1))
        pure ()
      | .var_ty x1, .var_ty x2 =>
        emit (x1 = x2)
      | .Public, .Public => pure ()
      | .var_ty x, t' => check_subtype n Phi Psi Delta (Delta x) t'
      | .Public, .Data l1 => pure ()
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
        emit (u = v)
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
        let constraint_holds := extended_phi |= constraint
        let extended_psi := lift_psi Psi
        let extended_delta := lift_delta_l Delta
        check_subtype n extended_phi extended_psi extended_delta t t'
        emit (cs = cs')
      | .t_if lab t1 t2, t' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta t1 t'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta t2 t'
      | t, .t_if lab t1' t2' => do
        check_subtype n Phi ((.corr lab) :: Psi) Delta t t1'
        check_subtype n Phi ((.not_corr lab) :: Psi) Delta t t2'
      | _, _ => throw ()


@[simp]
def from_synth (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (t : ty l d) (exp : Option (ty l d)) :
          Check (ty l d) :=
    match exp with
    | .none => pure t
    | .some t' => do
      check_subtype subtype_fuel Phi Psi Delta t t'
      pure t'


def to_data (fuel : Nat) (Delta : delta_context l d) (t : ty l d)
  : Check (Owl.label l) :=
    match fuel with
    | 0 => throw ()
    | n + 1 =>
      match t with
      | .Data l1 => pure l1
      | .Public => pure (.latl L.bot)
      | .var_ty x => to_data n Delta (Delta x)
      | _ => throw ()


-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"
-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type
def infer (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          Check (ty l d) :=
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
      emit (Phi |= (.condition .leq l2 l1))
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
    | _ => throw ()
  | .assign e1 e2 => do
    let t0 <- infer Phi Psi Delta Gamma e1 .none
    match t0 with
    | .Ref t1 => do
      let _ <- infer Phi Psi Delta Gamma e2 (.some t1)
      from_synth Phi Psi Delta .Unit exp
    | _ => throw ()
  | .inl e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Gamma e (.some t1)
       pure (.sum t1 t2)
    | _ => throw ()
  | .inr e =>
    match exp with
    | .some (.sum t1 t2) => do
       let _ <- infer Phi Psi Delta Gamma e (.some t2)
       pure (.sum t1 t2)
    | _ => throw ()
  | .fixlam e =>
    match exp with
    | .some (.arr t t') => do
       let extended_gamma := cons (.arr t t') (cons t Gamma)
       let _ <- infer Phi Psi Delta extended_gamma e (.some t')
       pure (.arr t t')
    | _ => throw ()
  | .app e1 e2 =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Gamma e1 .none with
      | .arr t t' => do
        let _ <- infer Phi Psi Delta Gamma e2 (.some t)
        pure t'
      | _ => throw ()
    | .some expected => do
      let t1 <- infer Phi Psi Delta Gamma e2 .none
      infer Phi Psi Delta Gamma e1 (.some (.arr t1 expected))
  | .tm_pair e1 e2 => do
    let t1 <- infer Phi Psi Delta Gamma e1 .none
    let t2 <- infer Phi Psi Delta Gamma e2 .none
    from_synth Phi Psi Delta (.prod t1 t2) exp
  | .left_tm e => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .prod t1 t2 => from_synth Phi Psi Delta t1 exp
    | _ => throw ()
  | .right_tm e => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .prod t1 t2 => from_synth Phi Psi Delta t2 exp
    | _ => throw ()
  | .case e e1 e2 => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .sum t1 t2 => do
      let r1 <- infer Phi Psi Delta (cons t1 Gamma) e1 (.some t1)
      let r2 <- infer Phi Psi Delta (cons t2 Gamma) e2 (.some t2)
      match exp with
      | .some res =>  do
        check_subtype subtype_fuel Phi Psi Delta r1 res
        check_subtype subtype_fuel Phi Psi Delta r2 res
        pure res
      | none => do
        check_subtype subtype_fuel Phi Psi Delta r2 r1
        pure r1
    | _ => throw ()
  | .tlam e =>
    match exp with
    | .some (.all t0 t) => do
      let _ <- infer Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t)
      pure (.all t0 t)
    | _ => throw ()
  | .tapp e t' => do
    match <- infer Phi Psi Delta Gamma e .none with
    | .all t0 t => do
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let result_ty := subst_ty .var_label (cons t' .var_ty) t;
      from_synth Phi Psi Delta result_ty exp
    | _ => throw ()
  | .pack t' e =>
    match exp with
    | .none => throw ()
    | .some (.ex t0 t) => do
      let substituted_type := subst_ty .var_label (cons t' .var_ty) t
      check_subtype subtype_fuel Phi Psi Delta t' t0
      let r <- infer Phi Psi Delta Gamma e (.some substituted_type)
      pure (.ex t0 t)
    | _ => throw ()
  | .unpack e e' =>
    match exp with
    | .none => throw ()
    | .some exp_ty => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .ex t0 t => do
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id shift exp_ty
        let res <- infer Phi Psi extended_delta extended_gamma e' (.some renamed_t')
        pure exp_ty
      | _ => throw ()
  | .l_lam e =>
    match exp with
    | .none => throw ()
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body => do
        let _ <- infer (lift_phi ((cons (cs, lab)) Phi))
                  (lift_psi Psi)
                  (lift_delta_l Delta) (lift_gamma_l Gamma)
                  e (.some t_body)
        pure exp_ty
      | _ => throw ()
  | .lapp e lab' =>
    match exp with
    | .none => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .all_l cs lab t  => do
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        let constraint_obligation := (Phi |= (.condition cs lab lab'))
        emit constraint_obligation
        pure result_ty
      | _ => throw ()
    | .some exp_ty => do
      match <- infer Phi Psi Delta Gamma e .none with
      | .all_l cs lab t => do
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        check_subtype subtype_fuel Phi Psi Delta result_ty exp_ty
        let constraint_obligation := (Phi |= (.condition cs lab lab'))
        emit constraint_obligation
        pure exp_ty
      | _ => throw ()
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
      check_subtype subtype_fuel Phi psi_not_corr Delta t2 t1
      pure t1
    | .some exp_ty =>do
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      let _ <- infer Phi psi_corr Delta Gamma e (.some exp_ty)
      let _ <- infer Phi psi_not_corr Delta Gamma e (.some exp_ty)
      pure exp_ty
  | .sync e => do
    let _ <- infer Phi Psi Delta Gamma e (.some .Public)
    from_synth Phi Psi Delta .Public exp
  | _ => throw ()

def has_type_infer Phi Psi Delta Gamma (e : tm l d m) (exp : ty l d) :=
  match (infer Phi Psi Delta Gamma e (.some exp)).run True with
  | .ok _ p => p
  | .error _ _ => False

theorem infer_sound Phi Psi Delta Gamma (e : tm l d m) (exp : ty l d) :
  has_type_infer Phi Psi Delta Gamma e exp ->
  has_type Phi Psi Delta Gamma e exp := by
    sorry

end OwlTc
