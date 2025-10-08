import OwlLean.OwlLang.Owl
import Lean

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

def gamma_context (l : Nat) (d : Nat) (m : Nat) := Fin m -> ty l d
def delta_context (l : Nat) (d : Nat) := Fin d -> ty l d
def phi_context (l : Nat) := Fin l -> (cond_sym × label l)

def empty_gamma : gamma_context l d 0 :=
  fun (i : Fin 0) => nomatch i

def empty_delta : delta_context l 0 :=
  fun (i : Fin 0) => nomatch i

def empty_phi : (phi_context 0) :=
  fun (i : Fin 0) => nomatch i

def lift_delta (Delta : Fin (d + 1) -> ty l d)
  : delta_context l (d + 1)
  := fun i => ren_ty id shift (Delta i)

def lift_delta_l (Delta : delta_context l d)
  : delta_context (l + 1) d
  := fun i => ren_ty shift id (Delta i)

def lift_gamma_d (Gamma : gamma_context l d m)
  : gamma_context l (d + 1) m
  := fun i => ren_ty id shift (Gamma i)

def lift_gamma_l (Gamma : gamma_context l d m)
  : gamma_context (l + 1) d m
  := fun i => ren_ty shift id (Gamma i)

-- Convert from labels down to lattice elements
noncomputable def interp_lattice (l : label 0) : L.labels :=
  match l with
  | .latl x => x
  | .ljoin x y => (L.join (interp_lattice x) (interp_lattice y))
  | .lmeet x y => (L.meet (interp_lattice x) (interp_lattice y))
  | .var_label n => nomatch n
  | .default => L.bot

def negate_cond (co : constr l) : constr l :=
  match co with
  | (.condition .leq x y) => (.condition .nleq x y)
  | (.condition .geq x y) => (.condition .ngeq x y)
  | (.condition .gt x y) => (.condition .ngt x y)
  | (.condition .lt x y) => (.condition .nlt x y)
  | (.condition .nleq x y) => (.condition .leq x y)
  | (.condition .ngeq x y) => (.condition .geq x y)
  | (.condition .ngt x y) => (.condition .gt x y)
  | (.condition .nlt x y) => (.condition .lt x y)

-- Check if a constraint is valid, under the assumption it is closed *)
def valid_constraint (co : constr 0) : Prop :=
  match co with
  | (.condition .leq x y) => L.leq (interp_lattice x) (interp_lattice y) = true
  | (.condition .geq x y) => L.leq (interp_lattice y) (interp_lattice x) = true
  | (.condition .gt x y) => L.leq (interp_lattice y) (interp_lattice x) = true /\ L.leq (interp_lattice x) (interp_lattice y) = false
  | (.condition .lt x y) => L.leq (interp_lattice x) (interp_lattice y) = true /\ L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .nleq x y) => L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .ngeq x y) => L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .ngt x y) => L.leq (interp_lattice y) (interp_lattice x) = false \/ L.leq (interp_lattice x) (interp_lattice y) = true
  | (.condition .nlt x y) => L.leq (interp_lattice x) (interp_lattice y) = false \/ L.leq (interp_lattice y) (interp_lattice x) = false


def phi_map (l : Nat) : Type := (Fin l) -> (label 0)
def empty_phi_map : phi_map 0 := fun (i : Fin 0) => nomatch i

def phi_map_holds (l : Nat) (pm : phi_map l) (co : constr l) : Prop :=
  match co with
  | (.condition c l1 l2) => (valid_constraint (.condition c (subst_label pm l1) (subst_label pm l2)))

def lift_phi (pm : Fin (l + 1) -> (cond_sym × label l)) : phi_context (l + 1) :=
  fun i =>
    let ⟨sym, lab⟩ := (pm i)
    ⟨sym, ren_label shift lab⟩

def pcons (x : cond_sym × label l) (phi : phi_context l) : phi_context (l + 1) :=
  (lift_phi (cons x phi))

def dcons (x : ty l d) (delta : delta_context l d) : delta_context l (d+1) :=
  (lift_delta (cons x delta))

inductive valid_phi_map : forall l, phi_map l -> phi_context l -> Prop where
| phi_empty_valid : valid_phi_map 0 empty_phi_map empty_phi
| phi_cons : forall l pm phictx phi (sym : cond_sym) (lab : label l) (lab_val : label 0),
  valid_phi_map l pm phictx ->
  phi_map_holds (l+1) (cons lab_val pm) (.condition sym (.var_label var_zero) (ren_label shift lab)) ->
  phi = lift_phi (cons (sym, lab) phictx) ->
  valid_phi_map (l+1) (cons lab_val pm) phi

def phi_entails_c (pctx : phi_context l) (co : constr l) : Prop :=
  (forall pm,
    valid_phi_map l pm pctx ->
    phi_map_holds l pm co)

notation:100 pctx " |= " co => phi_entails_c pctx co

notation:100 "! " e => tm.dealloc e

-- Checks for proper values within terms
inductive is_value : tm l d m -> Prop where
| error_value : is_value .error
| skip_value : is_value .skip
| loc_value : forall n,
  is_value (.loc n)
| bitstring_value : forall b,
  is_value (.bitstring b)
| fixlam_value : forall e,
  is_value (.fixlam e)
| pair_value : forall v1 v2,
  is_value v1 ->
  is_value v2 ->
  is_value (.tm_pair v1 v2)
| inl_value : forall v,
  is_value v ->
  is_value (.inl v)
| inr_value : forall v,
  is_value v ->
  is_value (.inr v)
| tlam_value : forall e,
  is_value (.tlam e)
| l_lam_value : forall e,
  is_value (.l_lam e)
| pack_value : forall t v,
  is_value v ->
  is_value (.pack t v)

  -- subtyping rules for Owl
  inductive subtype : (phi_context l) -> (delta_context l d) ->
      ty l d -> ty l d -> Prop where
  | ST_Var : forall x t',
    subtype Phi Delta (Delta x) t' ->
    subtype Phi Delta (.var_ty x) t'
  | ST_Any : forall t,
    subtype Phi Delta t .Any
  | ST_Unit : subtype Phi Delta .Unit .Unit
  | ST_Data : forall lab lab',
    (Phi |= (.condition .leq lab lab')) ->
    subtype Phi Delta (.Data lab) (.Data lab')
  | ST_RPublic : forall lab,
    subtype Phi Delta .Public (.Data lab)
  | ST_Func : forall t1' t1 t2 t2',
    subtype Phi Delta t1' t1 ->
    subtype Phi Delta t2 t2' ->
    subtype Phi Delta (.arr t1 t2) (.arr t1' t2')
  | ST_Prod : forall t1 t1' t2 t2',
    subtype Phi Delta t1 t1' ->
    subtype Phi Delta t2 t2' ->
    subtype Phi Delta (.prod t1 t2) (.prod t1' t2')
  | ST_Sum : forall t1 t1' t2 t2',
    subtype Phi Delta t1 t1' ->
    subtype Phi Delta t2 t2' ->
    subtype Phi Delta (.sum t1 t2) (.sum t1' t2')
  | ST_Ref : forall t,
    subtype Phi Delta (.Ref t) (.Ref t)
  | ST_Univ : forall t0 t0' t t',
    subtype Phi Delta t0 t0' ->
    subtype Phi (lift_delta (cons t0' Delta)) t t' ->
    subtype Phi Delta (.all t0 t) (.all t0' t')
  | ST_Exist : forall t0 t0' t t',
    subtype Phi Delta t0 t0' ->
    subtype Phi (lift_delta (cons t0 Delta)) t t' ->
    subtype Phi Delta (.ex t0 t) (.ex t0' t')
  | ST_LatUniv : forall cs lab lab' t t',
    ((lift_phi (cons (cs, lab) Phi))
    |= (.condition cs (.var_label var_zero) (ren_label shift lab'))) ->
    subtype (lift_phi (cons (cs, lab) Phi)) (lift_delta_l Delta) t t' ->
    subtype Phi Delta (.all_l cs lab t) (.all_l cs lab' t')
  | ST_IfElimL : forall co t1 t2 t1',
    (Phi |= co) ->
    subtype Phi Delta t1 t1' ->
    subtype Phi Delta (.t_if co t1 t2) t1'
  | ST_IfElimR : forall co t1 t2 t2',
    (Phi |= (negate_cond co)) ->
    subtype Phi Delta t2 t2' ->
    subtype Phi Delta (.t_if co t1 t2) t2'
  | ST_IfIntroL : forall co t1 t1' t2',
    (Phi |= co) ->
    subtype Phi Delta t1 t1' ->
    subtype Phi Delta t1 (.t_if co t1' t2')
  | ST_IfIntroR : forall co t2 t1' t2',
    (Phi |= (negate_cond co)) ->
    subtype Phi Delta t2 t2' ->
    subtype Phi Delta t2 (.t_if co t1' t2')
  | ST_Public :
    subtype Phi Delta .Public .Public

-- Typing rules for Owl
inductive has_type : (Phi : phi_context l) -> (Delta : delta_context l d) -> (Gamma : gamma_context l d m) ->
  tm l d m -> ty l d -> Prop where
| T_Var : forall x,
  has_type  Phi Delta Gamma (.var_tm x) (Gamma x)
| T_IUnit : has_type  Phi Delta Gamma .skip .Unit
| T_Const : forall b,
  has_type  Phi Delta Gamma (.bitstring b) .Public
| T_Op : forall op e1 e2 l,
  has_type  Phi Delta Gamma e1 (.Data l) ->
  has_type  Phi Delta Gamma e2 (.Data l) ->
  has_type  Phi Delta Gamma (.Op op e1 e2) (.Data l)
| T_Zero : forall e l,
  has_type  Phi Delta Gamma e (.Data l) ->
  has_type  Phi Delta Gamma (.zero e) .Public
| T_If : forall e e1 e2 t,
  has_type Phi Delta Gamma e .Public ->
  has_type Phi Delta Gamma e1 t ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.if_tm e e1 e2) t
| T_IRef : forall e t,
  has_type  Phi Delta Gamma e t ->
  has_type  Phi Delta Gamma (.alloc e) (.Ref t)
| T_ERef : forall e t,
  has_type  Phi Delta Gamma e (.Ref t) ->
  has_type  Phi Delta Gamma (! e) t
| T_Assign : forall e1 e2 t,
  has_type  Phi Delta Gamma e1 (.Ref t) ->
  has_type  Phi Delta Gamma e2 t ->
  has_type  Phi Delta Gamma (.assign e1 e2) .Unit
| T_IFun : forall e t t',
  has_type  Phi Delta (cons (.arr t t') (cons t Gamma)) e t' ->
  has_type  Phi Delta Gamma (.fixlam e) (.arr t t')
| T_EFun : forall e1 e2 t t',
  has_type  Phi Delta Gamma e1 (.arr t t') ->
  has_type  Phi Delta Gamma e2 t ->
  has_type  Phi Delta Gamma (.app e1 e2) t'
| T_IProd : forall e1 e2 t1 t2,
  has_type  Phi Delta Gamma e1 t1 ->
  has_type  Phi Delta Gamma e2 t2 ->
  has_type  Phi Delta Gamma (.tm_pair e1 e2) (.prod t1 t2)
| T_EProdL : forall e t1 t2,
  has_type  Phi Delta Gamma e (.prod t1 t2) ->
  has_type  Phi Delta Gamma (.left_tm e) t1
| T_EProdR : forall e t1 t2,
  has_type  Phi Delta Gamma e (.prod t1 t2) ->
  has_type  Phi Delta Gamma (.right_tm e) t2
| T_ISumL : forall e t1 t2,
  has_type  Phi Delta Gamma e t1 ->
  has_type  Phi Delta Gamma (.inl e) (.sum t1 t2)
| T_ISumR : forall e t1 t2,
  has_type  Phi Delta Gamma e t2 ->
  has_type  Phi Delta Gamma (.inr e) (.sum t1 t2)
| T_ESum : forall e t1 t2 t e1 e2,
  has_type  Phi Delta Gamma e (.sum t1 t2) ->
  has_type  Phi Delta (cons t1 Gamma) e1 t ->
  has_type  Phi Delta (cons t2 Gamma) e2 t ->
  has_type  Phi Delta Gamma (.case e e1 e2) t
| T_IUniv : forall t0 t e,
  has_type  Phi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e t ->
  has_type  Phi Delta Gamma (.tlam e) (.all t0 t)
| T_EUniv : forall t t' t0 e,
  subtype Phi Delta t' t0 ->
  has_type  Phi Delta Gamma e (.all t0 t) ->
  has_type  Phi Delta Gamma (.tapp e t') (subst_ty .var_label (cons t' .var_ty) t)
| T_IExist : forall e t t' t0,
  has_type  Phi Delta Gamma e (subst_ty .var_label (cons t' .var_ty) t) ->
  subtype  Phi Delta t' t0 ->
  has_type  Phi Delta Gamma (.pack t' e) (.ex t0 t)
| T_EExist : forall e e' t0 t t',
  has_type  Phi Delta Gamma e (.ex t0 t) ->
  has_type Phi (lift_delta (cons t0 Delta)) (cons t (lift_gamma_d Gamma)) e' (ren_ty id shift t') ->
  has_type  Phi Delta Gamma (.unpack e e') t'
| T_ILUniv : forall cs lab e t,
  has_type (lift_phi ((cons (cs, lab)) Phi))
           (lift_delta_l Delta) (lift_gamma_l Gamma) e t ->
  has_type  Phi Delta Gamma (.l_lam e) (.all_l cs lab t)
| T_ELUniv : forall cs lab lab' e t,
  (Phi |= (.condition cs lab lab')) ->
  has_type  Phi Delta Gamma e (.all_l cs lab t) ->
  has_type  Phi Delta Gamma (.lapp e lab') (subst_ty (cons lab' .var_label) .var_ty t)
| T_Sync : forall e,
  has_type  Phi Delta Gamma e .Public ->
  has_type  Phi Delta Gamma (.sync e) .Public
| T_Sub : forall e t t',
  subtype Phi Delta t t' ->
  has_type  Phi Delta Gamma e t ->
  has_type  Phi Delta Gamma e t'
| T_Annot : forall e t,
  has_type  Phi Delta Gamma e t ->
  has_type  Phi Delta Gamma (.annot e t) t

-- NEED TO ADD IF STATEMENTS BACK (RELFLECTING NEW CORR DEFS)

theorem simple_var_typing :
  forall x  Phi Delta (Gamma : gamma_context l d m),
     has_type  Phi Delta Gamma (.var_tm x) (Gamma x) := by
  intro x  Phi Delta Gamma
  exact has_type.T_Var x

theorem concrete_typing : @has_type 0 0 0  empty_phi empty_delta empty_gamma .skip .Unit :=
  has_type.T_IUnit

noncomputable def infer_type (Gamma : gamma_context l d m) (e : tm l d m) : (ty l d) :=
    match e with
    | .var_tm n => (Gamma n)
    | .skip => .Unit
    | .bitstring _ => (.Data (.latl L.bot))
    | _ => .default


-- NEEDED TACTICS
-- has_type
-- subtype
-- phi_entails_c

-- search for a subtype???

-- Give Tlam a subtyping

-- CLAIMS
-- 1. SUBTYPING WILL JUST WORK ON ITS OWN BY BEING THE LAST RULE AND INFERRING
-- 2. LABEL CONSTRAINTS CAN BE ASSUMED AS L.BOT, AND SUBTYPES CAN BE ASSUMED TO HAVE UPPER BOUNDS OF "ANY"

-- TODO
-- check/synthesize
-- Annotation (for synthesis) + *maybe* subtyping notation

-- ALL NEW *Infer* function!!!
structure Conditional (p : Prop) where
  side_condition : Prop
  side_condition_sound : side_condition -> p

structure CheckType (Phi : phi_context l) (Delta : delta_context l d)
                     (Gamma : gamma_context l d m) (e : tm l d m) (exp : ty l d) : Type where
  check : has_type  Phi Delta Gamma e exp

structure STType (Phi : phi_context l) (Delta : delta_context l d)
                     (t1 : ty l d) (t2 : ty l d) : Type where
  st : subtype Phi Delta t1 t2

notation:100  "grind" ck => (Conditional.side_condition_sound ck (by grind))


-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!

def check_subtype  (fuel : Nat) (Phi : phi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : Option (Conditional (subtype Phi Delta t1 t2)) :=
    match fuel with
    | 0 => .none
    | (n + 1) =>
      match t1, t2 with
      | x, .Any => .some ⟨True, fun _ => subtype.ST_Any x⟩
      | .Unit, .Unit => .some ⟨True, fun _ => subtype.ST_Unit⟩
      | .Data l1, .Data l2 => .some ⟨(Phi |= (.condition .leq l1 l2)), fun sc => subtype.ST_Data l1 l2 sc⟩
      | .Data l1, .Public => sorry
      | .Public, .Public => .some ⟨True, fun _ => subtype.ST_Public⟩
      | .var_ty x, t' =>
          match check_subtype n Phi Delta (Delta x) t' with
          | .some pf =>
            .some ⟨pf.side_condition,
                  fun sc => subtype.ST_Var x t' (grind pf)⟩
          | .none => .none
      | .Public, .Data l1 =>
        .some ⟨True, fun _ => subtype.ST_RPublic l1⟩
      | (.arr t1 t2), (.arr t1' t2') =>
        match check_subtype n Phi Delta t1' t1, check_subtype n Phi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Func t1' t1 t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | (.prod t1 t2), (.prod t1' t2') =>
        match check_subtype n Phi Delta t1 t1', check_subtype n Phi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Prod t1 t1' t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | (.sum t1 t2), (.sum t1' t2') =>
        match check_subtype n Phi Delta t1 t1', check_subtype n Phi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Sum t1 t1' t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | .Ref u, .Ref v =>
        .some ⟨(u = v), by
          intro h
          cases h
          exact subtype.ST_Ref u⟩
      | _, _ => .none

-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"
-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type
def infer (Phi : phi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          Option (match exp with
                  | .none => ((t : ty l d) × Conditional (has_type  Phi Delta Gamma e t))
                  | .some exp' => Conditional (has_type  Phi Delta Gamma e exp')) :=
  match e with
  | .var_tm x =>
    match exp with
    | .none =>
        let proof := fun _ => has_type.T_Var x
        .some ⟨(Gamma x), ⟨True, proof⟩⟩
    | .some t =>
      let et1 := (Gamma x)
      let et2 := has_type.T_Var x
      let es := check_subtype 99 Phi Delta (Gamma x) t
      match es with
      | .some es' =>
        .some ⟨es'.side_condition, fun sc => has_type.T_Sub (.var_tm x) et1 t (grind es') et2⟩
      | .none => .none
  | .skip =>
    match exp with
    | .none => .some ⟨.Unit, ⟨True, fun _ => has_type.T_IUnit⟩⟩
    | .some t =>
      match (check_subtype 99 Phi Delta .Unit t) with
      | .some pf =>
        .some ⟨pf.side_condition,
              fun sc =>
                has_type.T_Sub .skip .Unit t (pf.side_condition_sound sc) has_type.T_IUnit⟩
      | .none => .none
  | .bitstring b =>
    match exp with
    | .none => .some ⟨.Public, ⟨True, fun _ => has_type.T_Const b⟩⟩
    | .some t =>
      match (check_subtype 99 Phi Delta .Public t) with
      | .some pf =>
        .some ⟨pf.side_condition,
               fun sc => has_type.T_Sub (.bitstring b) .Public t (pf.side_condition_sound sc) (has_type.T_Const b)⟩
      | .none => .none
  | .Op op e1 e2 =>
    match exp with
    | .none => -- try to synthesize
      match infer  Phi Delta Gamma e1 .none with -- find type of e1
      | .some ⟨.Data l1, pf1⟩ =>
        match infer  Phi Delta Gamma e2 (.some (.Data l1)) with
        | .some e2pf =>
          .some ⟨.Data l1,
                 ⟨pf1.side_condition /\ e2pf.side_condition,
                  fun sc => has_type.T_Op op e1 e2 l1 (pf1.side_condition_sound (by grind)) (e2pf.side_condition_sound (by grind))⟩⟩
        | .none =>
          match infer  Phi Delta Gamma e2 .none with  -- find type of e2
          | .some ⟨.Data l2, pf2⟩ =>
            match infer  Phi Delta Gamma e1 (.some (.Data l2)) with
            | .some e1pf =>
              .some ⟨.Data l2,
                     ⟨e1pf.side_condition /\ pf2.side_condition,
                      fun sc => has_type.T_Op op e1 e2 l2 (e1pf.side_condition_sound (by grind)) (pf2.side_condition_sound (by grind))⟩⟩
            | .none => .none
          | _ => .none
      | _ => .none
    | .some t =>
      match t with
      | .Data l =>
        match infer  Phi Delta Gamma e1 (.some (.Data l)) with
        | .some pf1 =>
          match infer  Phi Delta Gamma e2 (.some (.Data l)) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_Op op e1 e2 l (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .zero e =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
            .some ⟨.Public,
                   ⟨pf.side_condition, fun sc => has_type.T_Zero e l (pf.side_condition_sound (by grind))⟩⟩
      | _ => .none
    | .some t =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
        match check_subtype 99 Phi Delta .Public t with
        | .some sub =>
          .some ⟨pf.side_condition /\ sub.side_condition,
                fun sc => has_type.T_Sub (.zero e) .Public t (grind sub) (has_type.T_Zero e l (grind pf))⟩
        | .none => .none
      | _ => .none
  | .if_tm e e1 e2 =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.Public, cond_pf⟩ =>
        match infer  Phi Delta Gamma e1 .none with
        | .some ⟨t1, pf1⟩ =>
          match infer  Phi Delta Gamma e2 (.some t1) with
          | .some pf2 =>
            .some ⟨t1,
                  ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_If e e1 e2 t1 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
          | .none =>
            match infer  Phi Delta Gamma e2 .none with
            | .some ⟨t2, pf2⟩ =>
              match infer  Phi Delta Gamma e1 (.some t2) with
              | .some pf1 =>
                .some ⟨t2, ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                       fun sc => has_type.T_If e e1 e2 t2 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some t =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.Public, cond_pf⟩ =>
        match infer  Phi Delta Gamma e1 (.some t) with
        | .some pf1 =>
           match infer  Phi Delta Gamma e2 (.some t) with
           | .some pf2 =>
             .some ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition ,
                    fun sc => has_type.T_If e e1 e2 t (grind cond_pf) (grind pf1) (grind pf2)⟩
           | .none => .none
        | .none => .none
      | _ => .none
  | .alloc e =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨t, pf⟩ =>
        .some ⟨.Ref t, ⟨pf.side_condition, fun sc =>has_type.T_IRef e t (grind pf)⟩⟩
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .Ref t =>
        match infer  Phi Delta Gamma e (.some t) with
        | .some pf => .some ⟨pf.side_condition, fun sc => has_type.T_IRef e t (grind pf)⟩
        | .none => .none
      | _ => .none
  | .dealloc e =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.Ref t, pf⟩ =>
        .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_ERef e t (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e (.some (.Ref exp_ty)) with
      | .some pf => .some ⟨pf.side_condition , fun sc => has_type.T_ERef e exp_ty (grind pf)⟩
      | .none => .none
  | .assign e1 e2 =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e1 .none with
      | .some ⟨.Ref t, pf1⟩ =>
        match infer  Phi Delta Gamma e2 (.some t) with
        | .some pf2 =>
          .some ⟨.Unit, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_Assign e1 e2 t (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match exp_ty with
      | .Unit =>
        match infer  Phi Delta Gamma e1 .none with
        | .some ⟨.Ref t, pf1⟩ =>
          match infer  Phi Delta Gamma e2 (.some t) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_Assign e1 e2 t (grind pf1) (grind pf2)⟩
          | .none => .none
        | _ => .none
      | _ => .none
  | .inl e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort!
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer  Phi Delta Gamma e (.some t1) with
        | .some pr => .some ⟨pr.side_condition, fun sc => has_type.T_ISumL e t1 t2 (grind pr)⟩
        | .none => .none
      | _ => .none
  | .inr e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort!
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer  Phi Delta Gamma e (.some t2) with
        | .some pr => .some ⟨pr.side_condition, fun sc => has_type.T_ISumR e t1 t2 (grind pr)⟩
        | .none => .none
      | _ => .none
  | .fixlam e =>
    match exp with
    | .none => .none -- TODO, allow synthesis
    | .some t =>
      match t with
      | .arr t t' =>
        let extended_gamma := cons (.arr t t') (cons t Gamma)
        match infer  Phi Delta extended_gamma e (.some t') with
        | .some pe => .some ⟨pe.side_condition, fun sc => has_type.T_IFun e t t' (grind pe)⟩
        | .none => .none
      | _ => .none
  | .app e1 e2 =>
    match exp with
    | .none => -- synthesize
      match infer  Phi Delta Gamma e1 .none with
      | .some ⟨ty1, pf1⟩ =>
        match ty1 with
        | .arr t t' =>
          match infer  Phi Delta Gamma e2 (.some t) with
          | .some pf2 => .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_EFun e1 e2 t t' (grind pf1) (grind pf2)⟩⟩
          | .none => .none
        | _ => .none
      | .none => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e1 .none with -- synthesize a type for e1
      | .some ⟨ty1, pf1⟩ =>
        match ty1 with
            | .arr t t' => -- correct type synthesized
              match infer  Phi Delta Gamma e2 (some t) with -- check type of e2
              | .some pf2 =>
                let sub := check_subtype 99 Phi Delta t' exp_ty -- check that t' is a subtype of exp_ty
                match sub with
                | .some sub' =>
                    .some ⟨pf1.side_condition /\ pf2.side_condition /\ sub'.side_condition,
                           fun sc => has_type.T_Sub (.app e1 e2) t' exp_ty (grind sub') (has_type.T_EFun e1 e2 t t' (grind pf1) (grind pf2))⟩ -- proof that |- e1 e2 : exp_ty
                | .none => .none
              | .none => .none
            | _ => .none
      | .none => .none
  | .tm_pair e1 e2 =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e1 .none with
      | .some ⟨t1, pf1⟩ =>
        match infer  Phi Delta Gamma e2 .none with
        | .some ⟨t2, pf2⟩ =>
          .some ⟨.prod t1 t2, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .prod t1 t2 =>
        match infer  Phi Delta Gamma e1 (.some t1) with
        | .some pf1 =>
          match infer  Phi Delta Gamma e2 (.some t2) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .left_tm e =>
    match exp with
    | .none => -- synthesize
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t1, ⟨pf.side_condition, fun sc => has_type.T_EProdL e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype 99 Phi Delta t1 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition ,
                 fun sc => has_type.T_Sub (.left_tm e) t1 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdL e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .right_tm e =>
    match exp with
    | .none => -- synthesize
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t2, ⟨pf.side_condition, fun sc => has_type.T_EProdR e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype 99 Phi Delta t2 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition,
                 fun sc => has_type.T_Sub (.right_tm e) t2 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdR e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .case e e1 e2 =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer  Phi Delta (cons t1 Gamma) e1 .none with
        | .some ⟨t, pf2⟩ =>
          match infer  Phi Delta (cons t2 Gamma) e2 (.some t) with
          | .some pf3 =>
            .some ⟨t, ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                       fun sc =>
                         has_type.T_ESum e t1 t2 t e1 e2 (grind pf1) (grind pf2) (grind pf3)⟩⟩
          | .none =>
            match infer  Phi Delta (cons t2 Gamma) e2 .none with
            | .some ⟨t', pf2⟩ =>
              match infer  Phi Delta (cons t1 Gamma) e1 (.some t') with
              | .some pf3 =>
                .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                            fun sc =>
                              has_type.T_ESum e t1 t2 t' e1 e2 (grind pf1) (grind pf3) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer  Phi Delta (cons t1 Gamma) e1 (.some exp_ty) with
        | .some pf2 =>
          match infer  Phi Delta (cons t2 Gamma) e2 (.some exp_ty) with
          | .some pf3 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                  fun sc => has_type.T_ESum e t1 t2 exp_ty e1 e2 (grind pf1) (grind pf2) (grind pf3)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .tlam e =>
    match exp with
    | .none => .none  -- TODO : Synthesize!!!
    | .some (.all t0 t) =>
      match infer Phi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t) with
      | .some pf =>
        .some ⟨pf.side_condition,
                   fun sc => has_type.T_IUniv t0 t e (grind pf)⟩
      | .none => .none
    | _ => .none
  | .tapp e t' =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf1⟩ =>
        let sub := check_subtype 99 Phi Delta t' t0
        match sub with
        | .some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
         .some ⟨result_ty,
                  ⟨pf1.side_condition /\ sub'.side_condition,
                  fun sc => has_type.T_EUniv t t' t0 e (grind sub') (grind pf1)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf⟩ =>
        let sub := check_subtype 99 Phi Delta t' t0
        match sub with
        | some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
          let sub_result := check_subtype 99 Phi Delta result_ty exp_ty
          match sub_result with
          | .some sub_result' =>
            .some ⟨pf.side_condition /\ sub'.side_condition /\ sub_result'.side_condition,
                      fun sc =>
                        has_type.T_Sub (.tapp e t') result_ty exp_ty (grind sub_result')
                          (has_type.T_EUniv t t' t0 e (grind sub') (grind pf))⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .pack t' e =>
    match exp with
    | .none => .none -- TODO : potentially ADD Synthesis!
    | .some (.ex t0 t) =>
      let substituted_type := subst_ty .var_label (cons t' .var_ty) t
      match check_subtype 99 Phi Delta t' t0 with
      | .some sub =>
        match infer  Phi Delta Gamma e (.some substituted_type) with
        | .some pf =>
          .some ⟨pf.side_condition /\ sub.side_condition,
                 fun sc => has_type.T_IExist e t t' t0 (grind pf) (grind sub)⟩
        | .none => .none
      | .none => .none
    | _ => .none
  | .unpack e e' =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.ex t0 t, pf_e⟩ =>
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        match infer Phi extended_delta extended_gamma e' .none with
        | .some ⟨t', pf_e'⟩ =>
          .none -- TODO TEMP FOR NOW ; NEEDS UNSHIFTING
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.ex t0 t, pf_e⟩ =>
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id shift exp_ty
        match infer Phi extended_delta extended_gamma e' (.some renamed_t') with
        | .some pf_e' =>
                .some ⟨pf_e.side_condition /\ pf_e'.side_condition,
                       fun sc => has_type.T_EExist e e' t0 t exp_ty (grind pf_e) (grind pf_e')⟩
        | .none => .none
      | _ => .none
  | .l_lam e =>
    match exp with
    | .none => .none -- TODO NEED SYNTHESIS LATER (SUPPLY BOUND)
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body =>
         match infer (lift_phi ((cons (cs, lab)) Phi))
                  (lift_delta_l Delta) (lift_gamma_l Gamma)
                  e (.some t_body) with
         | .some pe =>
           .some ⟨pe.side_condition,
               fun sc => has_type.T_ILUniv cs lab e t_body (grind pe)⟩
         | .none => .none
      | _ => .none
  | .lapp e lab' =>
    match exp with
    | .none =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, pf⟩ =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        let constraint_obligation := (Phi |= (.condition cs lab lab'))
        .some ⟨result_ty,
              ⟨pf.side_condition /\ constraint_obligation,
                fun sc =>
                  has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer  Phi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, pf⟩ =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        match check_subtype 99 Phi Delta result_ty exp_ty with
        | .some sub_pf =>
          let constraint_obligation := (Phi |= (.condition cs lab lab'))
          .some ⟨pf.side_condition /\ constraint_obligation /\ sub_pf.side_condition,
                fun sc =>
                  has_type.T_Sub (.lapp e lab') result_ty exp_ty
                    (grind sub_pf)
                    (has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf))⟩
        | .none => .none
      | _ => .none
  | .annot e t =>
    match exp with
    | .none => -- synthesize a type
      match infer  Phi Delta Gamma e (.some t) with
      | .some pf => .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_Annot e t (grind pf)⟩⟩
      | .none => .none
    | .some exp_ty => -- check the type of annotation
      match check_subtype 99 Phi Delta t exp_ty with -- first check for subtype
      | .some sub =>
        match infer  Phi Delta Gamma e (.some t) with -- check that e has type t
        | .some pf =>
          .some ⟨sub.side_condition /\ pf.side_condition, fun sc => has_type.T_Sub (.annot e t) t exp_ty (grind sub) (has_type.T_Annot e t (grind pf))⟩
        | .none => .none
      | .none => .none
  | _ =>
    match exp with
    | .some _ => .none
    | .none => .none

syntax "tc_full" term:max term:max term:max term:max term:max tactic : tactic

open Lean Meta Elab Tactic

def simple_test_delta :=
   (dcons .Unit (@empty_delta 0))

def test_delta_2 :=
   (dcons (.var_ty ⟨0, by omega⟩) simple_test_delta)

noncomputable def simple_test_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩) (pcons (.geq, .latl L.bot) empty_phi))

noncomputable def simple_test_gamma : gamma_context 0 0 1 :=
  (cons .Unit empty_gamma)

theorem cons_surjective {n : Nat} (f : Fin (n + 1) → label 0) :
  ∃ (head : label 0) (tail : Fin n → label 0),
    f = cons head tail := by
  exists f 0
  exists (fun i => f i.succ)
  funext i
  cases i using Fin.cases
  · rfl
  · rfl

theorem ren_label_injective
  (h : forall x y, xi x = xi y -> x = y) :
  forall s1 s2, ren_label xi s1 = ren_label xi s2 → s1 = s2 := by
  intro s1 s2 heq
  induction s1 generalizing s2 with
  | var_label x =>
      cases s2 <;> simp [ren_label] at heq
      congr
      exact h _ _ heq
  | latl l =>
      cases s2 <;> simp [ren_label] at heq
      subst heq
      rfl
  | ljoin l1 l2 ih1 ih2 =>
      cases s2 <;> simp [ren_label] at heq
      congr
      · exact ih1 _ heq.1
      · exact ih2 _ heq.2
  | lmeet l1 l2 ih1 ih2 =>
      cases s2 <;> simp [ren_label] at heq
      congr
      · exact ih1 _ heq.1
      · exact ih2 _ heq.2
  | default =>
      cases s2 <;> simp [ren_label] at heq
      rfl

theorem shift_injective : forall (x : Fin l) (y : Fin l), shift x = shift y -> x = y := by
  intro x y h
  simp [shift] at h
  exact h

syntax "solve_phi_validation" ident : tactic
syntax "attempt_solve" : tactic
syntax "solve_phi_validation_anon" : tactic
syntax "solve_phi_validation_anon_no_simp" : tactic
syntax "case_phi " ident ident ident num num : tactic
syntax "all_ren" ident ident num num : tactic

macro_rules
  | `(tactic| all_ren $test:ident $inj:ident $curr:num $goal:num) => do
      let suf := "_" ++ toString curr.getNat
      let mk (s : String) : TSyntax `ident := mkIdent <| Name.str .anonymous (s ++ suf)
      let eId := mk "e"
      let currVal := (curr.getNat)
      let currNextVal := (curr.getNat + 1)
      let currNextValSyntax := Syntax.mkNumLit (toString currNextVal)
      let goalVal := (goal.getNat)
      if currVal < goalVal then
        `(tactic|
          have $(eId):ident := ren_label_injective shift_injective _ _ $test:ident;
          all_ren $(eId):ident $inj:ident $currNextValSyntax $goal:num)
      else
        `(tactic|
          try rw [<- $test:ident] at $inj:ident)
  | `(tactic| solve_phi_validation $lemma_phi:ident) => `(tactic|
      intros pm vpm;
      trace "hi 1";
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label];
      unfold $lemma_phi:ident at vpm;
      simp at vpm;
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| attempt_solve) => `(tactic|
      intros pm vpm;
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label, interp_lattice];
      try grind
    )
  | `(tactic| solve_phi_validation_anon) => `(tactic|
      intros pm vpm;
      trace "hi 1";
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      unfold phi_map_holds;
      unfold valid_constraint;
      trace "hi 1.2";
      simp [subst_label];
      simp at vpm;
      trace "hi 1.5";
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| solve_phi_validation_anon_no_simp) => `(tactic|
      intros pm vpm;
      trace "hi 1";
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      unfold phi_map_holds;
      unfold valid_constraint;
      trace "hi 1.2";
      simp [subst_label];
      trace "hi 1.5";
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| case_phi $H:ident $A:ident $prevHold:ident $k:num $iter:num) => do
      let suf := "_" ++ toString k.getNat
      let iterVal := (iter.getNat)
      let newKVal := (k.getNat + 1)
      let prevKVal := (k.getNat - 1)
      let prevKValSyntax := Syntax.mkNumLit (toString prevKVal)
      let newIterVal := (iter.getNat + 1)
      let newIterSyntax := Syntax.mkNumLit (toString newIterVal)
      let newKSyntax := Syntax.mkNumLit (toString newKVal)
      let mk (s : String) : TSyntax `ident := mkIdent <| Name.str .anonymous (s ++ suf)
      let lId         := mk "l"
      let pmPrevId    := mk "pm_prev"
      let pctxPrevId  := mk "phictx_prev"
      let phiEqId     := mk "phi_eq"
      let symId       := mk "sym"
      let labId       := mk "lab"
      let labValId    := mk "lab_val"
      let tailId      := mk "vpm_tail"
      let headHoldsId := mk "head_holds"
      let aId       := mk "a"
      let hId := mk "h0"
      let labeqId := mk "lab_eq"
      if iterVal = 0 then
        `(tactic|
          cases $H:ident with
          | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                    $(symId):ident $(labId):ident $(labValId):ident
                    $(tailId):ident $(headHoldsId):ident $(aId):ident =>
              trace "hi 2";
              have h0 := congrArg (fun f => f 0) $(aId):ident
              simp [lift_phi, cons] at h0
              obtain ⟨sym_eq, lab_eq⟩ := h0
              unfold phi_map_holds at $(headHoldsId):ident
              unfold valid_constraint at $(headHoldsId):ident
              rw [<- lab_eq] at $(headHoldsId):ident
              try simp [ren_label, shift, cons, subst_label] at $(headHoldsId):ident
              simp [var_zero] at $(headHoldsId):ident
              case_phi $(tailId):ident $(aId):ident $(headHoldsId):ident $newKSyntax $newIterSyntax
        )
      else
        `(tactic|
         cases $H:ident with
          | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                    $(symId):ident $(labId):ident $(labValId):ident
                    $(tailId):ident $(headHoldsId):ident $(aId):ident =>
            trace "hi 3";
            rw [$(aId):ident] at $A:ident
            have $(hId):ident := congrArg (fun f => f $prevKValSyntax) $A:ident
            simp [lift_phi, cons] at $(hId):ident
            trace "hi 4";
            try obtain ⟨sym_eq, $(labeqId):ident⟩ := $(hId):ident
            simp at $(headHoldsId):ident
            trace "hi 5";
            unfold phi_map_holds at $(headHoldsId):ident
            unfold valid_constraint at $(headHoldsId):ident
            try all_ren $(labeqId):ident $(headHoldsId):ident 0 $prevKValSyntax:num
            try all_ren $(hId):ident $(headHoldsId):ident 0 $prevKValSyntax:num
            try simp [ren_label, shift, cons, subst_label] at $(headHoldsId):ident
            simp [var_zero] at $(headHoldsId):ident
            trace "hi 6";
            try simp [cons] at $(prevHold):ident
            trace "hi 7";
            try simp [cons]
            try grind [interp_lattice]
            try case_phi $(tailId):ident $(A):ident $(headHoldsId):ident $newKSyntax $newIterSyntax
        )

macro "solve_all_constraints" : tactic => `(tactic|
  repeat (first
    | constructor <;> (first
        | trivial
        | simp
        | attempt_solve
        | solve_phi_validation_anon
        | solve_phi_validation_anon_no_simp)))

macro_rules
  | `(tactic| tc_full $Phi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Delta $Gamma $e (some $t) with
      | some result =>
          cases result with
          | mk side_condition side_condition_sound =>
            cases h
            try dsimp at side_condition_sound
            apply side_condition_sound
            trace_state;
            solve_all_constraints;
            $k
      | none =>
          dsimp [infer] at h
          cases h
    )

syntax "tc" tactic:max : tactic
elab_rules : tactic
| `(tactic| tc $k) => do
  let g <- getMainGoal
  let ty <- g.getType
  let args := ty.getAppArgs
  let n := args.size
  let elems := args.extract (n-5) n
  let tac ← `(tactic| tc_full
                $(<- Term.exprToSyntax elems[0]!)
                $(<- Term.exprToSyntax elems[1]!)
                $(<- Term.exprToSyntax elems[2]!)
                $(<- Term.exprToSyntax elems[3]!)
                $(<- Term.exprToSyntax elems[4]!)
                $k)
  evalTactic tac

#reduce infer empty_phi empty_delta (cons .Unit empty_gamma) (.var_tm ⟨0, by omega⟩) (.some .Unit)

#reduce infer empty_phi empty_delta empty_gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.some (.arr .Unit .Unit))

theorem skip_has_unit_type (Phi : phi_context l) (Delta : delta_context l d)
                           (Gamma : gamma_context l d m) :
                           has_type  Phi Delta Gamma .skip .Any := by
  cases h : infer  Phi Delta Gamma .skip (.some .Any) with
  | some result =>
          dsimp [infer, check_subtype, cons] at h;
          cases result with
          | mk side_condition side_condition_sound =>
            cases h;
            apply side_condition_sound
            grind
  | none =>
          dsimp [infer, check_subtype] at h
          cases h

def packed_unit : tm l d m := .pack .Unit .skip

#reduce infer empty_phi empty_delta empty_gamma (.unpack (.annot packed_unit (.ex .Any .Unit)) .skip) (.some .Unit)

-- for label testing purposes!
theorem stub_label_flow : Phi |= constr.condition cond_sym.leq (label.latl l1) (label.latl l2) := by
  sorry

#reduce infer empty_phi empty_delta empty_gamma (.tm_pair (.alloc .skip) (.bitstring .bend)) (.some (.prod (.Ref .Unit) .Public))

theorem tc_ref_refl (Phi : phi_context l)
                    (Delta : delta_context l d) :
  has_type  Phi Delta (cons (.Ref (.prod .Unit .Unit)) empty_gamma)
    (tm.var_tm ⟨0, by omega⟩)
    (.Ref (.prod .Unit .Unit)) := by
  tc (try grind)

theorem tc_ref_refl2 (Phi : phi_context l)
                    (Delta : delta_context l d) (l1 l2 : L.labels) :
  has_type  Phi Delta (cons (.Ref (.Data (.latl l1))) empty_gamma)
    (tm.var_tm ⟨0, by omega⟩)
    (.Ref (.Data (.latl l1))) := by
  tc (try grind)

theorem tc_prod   (Phi : phi_context l)
                    (Delta : delta_context l d) (Gamma : gamma_context l d m) :
  has_type  Phi Delta Gamma
    (.tm_pair (.alloc .skip) (.bitstring .bend))
    (.prod (.Ref .Unit) (.Data (.latl l1))):= by
  tc (try grind)

theorem tc_label (Phi : phi_context l)
                         (Delta : delta_context l d) :
                         has_type  Phi Delta (cons (.Data (.latl l1)) empty_gamma)
                           (tm.var_tm ⟨0, by omega⟩)
                           (.Data (.latl l2)) := by
  tc (exact stub_label_flow)

theorem packed_unit_tc (Phi : phi_context l)
                         (Delta : delta_context l d) (Gamma : gamma_context l d m) :
                         has_type  Phi Delta (cons (.Data (.latl l1))  Gamma)
                           packed_unit
                           (.ex .Any .Unit) := by
  tc (try grind)

theorem unpack_packed_skip_alt :
  has_type empty_phi
           (dcons (.var_ty ⟨0, by omega⟩) (dcons .Unit empty_delta)) empty_gamma
           (.tapp
              (.annot (.tlam .skip) (.all .Any .Unit))
              (.var_ty ⟨1, by omega⟩))
           .Unit := by
  tc (try grind)


theorem pack_unit_exists (Phi : phi_context l)
                         (Delta : delta_context l d) (Gamma : gamma_context l d m) :
                         has_type  Phi Delta Gamma
                           (.pack .Unit (.tm_pair .skip .skip))
                           (.ex .Any (.prod (.var_ty 0) (.var_ty 0))) := by
  tc (try grind)

theorem lambda_simple (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type  Phi Delta Gamma (.fixlam (.alloc .skip)) (.arr .Unit (.Ref .Unit)) := by
  tc (try grind)

theorem lambda_identity_unit (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type  Phi Delta Gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.arr .Unit .Unit) := by
  tc (try grind)

-- Proof that injection into a larger goal works
theorem test_inject : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) /\ True := by
  apply And.intro
  unfold phi_entails_c
  intro pm vpm
  unfold phi_map_holds
  dsimp
  unfold valid_constraint
  dsimp
  simp [subst_label, interp_lattice]
  have lp : forall (l : L.labels), (L.leq L.bot l) = true := L.bot_proof
  apply (lp l1)
  trivial

theorem test_inject_2 : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) := by
  have ti : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) /\ True :=
    test_inject
  exact ti.left

-- Proof, that you can pass in a proof (proof of proof)
theorem bitstring_has_bot_type (Phi : phi_context l) (Delta : delta_context l d)
                                (Gamma : gamma_context l d m) (b : binary) :
                                has_type  Phi Delta Gamma (.bitstring b) (.Data (.latl l1)) := by
  tc (try grind)

-- Test theorem for inl with skip
theorem inl_skip_has_sum_type (Phi : phi_context l) (Delta : delta_context l d)
                              (Gamma : gamma_context l d m) (t2 : ty l d) :
                              has_type  Phi Delta Gamma (.inl .skip) (.sum .Unit t2) := by
  tc (try grind)

theorem fixlam_identity (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type  Phi Delta Gamma
                          (.fixlam .skip)
                          (.arr .Any .Unit) := by
  tc (try grind)

theorem pair_easy (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type  Phi Delta Gamma
                        (.tm_pair .skip .skip)
                        (.prod .Unit .Unit) := by
  tc (try grind)


noncomputable def lemma_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))
-- How I'd like to write it : (x, y >= x, z >= y, a >= z)

noncomputable def lemma_phi2 :=
  (pcons (.geq, .var_label ⟨2, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))

-- How I'd like to write it : (x, y >= x, z >= y, a >= x)

noncomputable def lemma_phi_mix (l1 l2 l3 : L.labels) :=
  (pcons (.geq, (.latl l1))
         (pcons (.geq, (.latl l2))
         (pcons (.geq, (.latl l3))
                (pcons (.geq, .latl L.bot) empty_phi))))

theorem test_latt :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨3, by omega⟩)) := by
    solve_phi_validation lemma_phi

theorem test_latt2 :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨2, by omega⟩)) := by
    solve_phi_validation lemma_phi

theorem test_latt3 :
  lemma_phi2 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨3, by omega⟩)) := by
    solve_phi_validation lemma_phi2

theorem test_latt_mix (l1 l2 l3 : L.labels) (pf1 : L.leq l1 l2 = true) (pf2 : L.leq l2 l3 = true):
  empty_phi |= (.condition .leq (.latl l1) (.latl l3)) := by
    attempt_solve

theorem test_latt_mix2 (l1 l2 l3 : L.labels) :
  lemma_phi_mix l1 l2 l3 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.latl l1)) := by
    solve_phi_validation lemma_phi_mix

-- Tedious example (non tactic)
theorem test_latt_manual (l1 l2 l3 : L.labels) (pf1 : L.leq l1 l2 = true) :
  lemma_phi_mix l1 l2 l3 |= (.condition .leq (.latl l1) (.latl l2)) := by
  intros pm vpm;
    have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
    unfold phi_map_holds;
    unfold valid_constraint;
    simp [subst_label];
    unfold lemma_phi_mix at vpm;
    unfold pcons at vpm;
  cases vpm with
  | phi_cons l1 pm_prev1 phictx_prev1 phi_eq1 sym1 lab1 lab_val1 h_prev1 h_holds1 a1 =>
    have h0 := congrArg (fun f => f 0) a1
    simp [lift_phi, cons] at h0
    obtain ⟨sym_eq, lab_eq⟩ := h0
    unfold phi_map_holds at h_holds1
    unfold valid_constraint at h_holds1
    rw [<- lab_eq] at h_holds1
    try simp [ren_label, cons, subst_label] at h_holds1
    simp [var_zero] at h_holds1
    cases h_prev1 with
    | phi_cons l2 pm_prev2 phictx_prev2 phi_eq2 sym2 lab2 lab_val2 h_prev2 h_holds2 a2 =>
      rw [a2] at a1
      have h0 := congrArg (fun f => f 1) a1
      simp [lift_phi, cons] at h0
      obtain ⟨sym_eq, lab_eq⟩ := h0
      simp at h_holds2
      unfold phi_map_holds at h_holds2
      unfold valid_constraint at h_holds2
      all_ren lab_eq h_holds2 0 1
      try simp [ren_label, cons, subst_label] at h_holds2
      simp [var_zero] at h_holds2
      try simp [cons] at h_holds1
      try simp [cons]
      try grind
      cases h_prev2 with
      | phi_cons l3 pm_prev3 phictx_prev3 phi_eq3 sym3 lab3 lab_val3 h_prev3 h_holds3 a3 =>
        rw [a3] at a1
        have h0 := congrArg (fun f => f 2) a1
        simp [lift_phi, cons] at h0
        obtain ⟨sym_eq, lab_eq⟩ := h0
        simp at h_holds3
        unfold phi_map_holds at h_holds3
        unfold valid_constraint at h_holds3
        all_ren lab_eq h_holds3 0 2
        try simp [ren_label, cons, subst_label] at h_holds3
        simp [var_zero] at h_holds3
        try simp [cons] at h_holds2
        try simp [cons]
        grind [interp_lattice]
