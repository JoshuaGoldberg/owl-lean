import OwlLean.OwlLang.Owl

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

def gamma_context (l : Nat) (d : Nat) (m : Nat) := Fin m -> ty l d
def delta_context (l : Nat) (d : Nat) := Fin d -> ty l d
def phi_context (l : Nat) := Fin l -> (cond_sym × label l)
def sigma_context (l : Nat) (d : Nat) := Nat -> Option (ty l d)

@[simp] theorem cons_zero {l d m} (t : ty l d) (Γ : gamma_context l d m) (h : 0 < m+1) :
  cons t Γ ⟨0, h⟩ = t := rfl

@[simp] theorem cons_succ {l d m} (t : ty l d) (Γ : gamma_context l d m)
  (k : Nat) (hk : k+1 < m+1) :
  cons t Γ ⟨k+1, hk⟩ = Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := rfl

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

inductive valid_phi_map : forall l, phi_map l -> phi_context l -> Prop where
| phi_empty_valid : valid_phi_map 0 empty_phi_map empty_phi
| phi_cons : forall l pm phictx (sym : cond_sym) (lab : label l) (lab_val : label 0),
  valid_phi_map l pm phictx ->
  phi_map_holds (l+1) (cons lab_val pm) (.condition sym (.var_label var_zero) (ren_label shift lab)) ->
  valid_phi_map (l+1) (cons lab_val pm) (lift_phi (cons (sym, lab) phictx))

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

def last_var l : Fin (l + 1) :=
  match l with
  | 0   => 0
  | n + 1 => (last_var n).succ

def adv (pf : l > 0) : label l :=
  match l with
  | 0 => by contradiction
  | n + 1 => .var_label (last_var n)

theorem three_proof :
  3 > 0 := by
    simp

-- Typing rules for Owl
inductive has_type : (Phi : phi_context l) -> (Delta : delta_context l d) -> (Gamma : gamma_context l d m) ->
  tm l d m -> ty l d -> Prop where
| T_Var : forall x,
  has_type Phi Delta Gamma (.var_tm x) (Gamma x)
| T_IUnit {Phi Delta Gamma} : has_type Phi Delta Gamma .skip .Unit
| T_Const : forall b,
  has_type Phi Delta Gamma (.bitstring b) .Public
| T_Op : forall op e1 e2 l,
  has_type Phi Delta Gamma e1 (.Data l) ->
  has_type Phi Delta Gamma e2 (.Data l) ->
  has_type Phi Delta Gamma (.Op op e1 e2) (.Data l)
| T_Zero : forall e l,
  has_type Phi Delta Gamma e (.Data l) ->
  has_type Phi Delta Gamma (.zero e) .Public
| T_If : forall e e1 e2 l t,
  has_type Phi Delta Gamma e (.Data l) ->
  has_type Phi Delta Gamma e1 t ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.if_tm e e1 e2) t
| T_IRef : forall e t,
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma (.alloc e) (.Ref t)
| T_ERef : forall e t,
  has_type Phi Delta Gamma e (.Ref t) ->
  has_type Phi Delta Gamma (! e) t
| T_Assign : forall e1 e2 t,
  has_type Phi Delta Gamma e1 (.Ref t) ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.assign e1 e2) .Unit
| T_IFun : forall e t t',
  has_type Phi Delta (cons (.arr t t') (cons t Gamma)) e t' ->
  has_type Phi Delta Gamma (.fixlam e) (.arr t t')
| T_EFun : forall e1 e2 t t',
  has_type Phi Delta Gamma e1 (.arr t t') ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.app e1 e2) t'
| T_IProd : forall e1 e2 t1 t2,
  has_type Phi Delta Gamma e1 t1 ->
  has_type Phi Delta Gamma e2 t2 ->
  has_type Phi Delta Gamma (.tm_pair e1 e2) (.prod t1 t2)
| T_EProdL : forall e t1 t2,
  has_type Phi Delta Gamma e (.prod t1 t2) ->
  has_type Phi Delta Gamma (.left_tm e) t1
| T_EProdR : forall e t1 t2,
  has_type Phi Delta Gamma e (.prod t1 t2) ->
  has_type Phi Delta Gamma (.right_tm e) t2
| T_ISumL : forall e t1 t2,
  has_type Phi Delta Gamma e t1 ->
  has_type Phi Delta Gamma (.inl e) (.sum t1 t2)
| T_ISumR : forall e t1 t2,
  has_type Phi Delta Gamma e t2 ->
  has_type Phi Delta Gamma (.inr e) (.sum t1 t2)
| T_ESum : forall e t1 t2 t e1 e2,
  has_type Phi Delta Gamma e (.sum t1 t2) ->
  has_type Phi Delta (cons t1 Gamma) e1 t ->
  has_type Phi Delta (cons t2 Gamma) e2 t ->
  has_type Phi Delta Gamma (.case e e1 e2) t
| T_IUniv : forall t0 t e,
  has_type Phi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e t ->
  has_type Phi Delta Gamma (.tlam e) (.all t0 t)
| T_EUniv : forall t t' t0 e,
  subtype Phi Delta t' t0 ->
  has_type Phi Delta Gamma e (.all t0 t) ->
  has_type Phi Delta Gamma (.tapp e t') (subst_ty .var_label (cons t' .var_ty) t)
| T_IExist : forall e t t' t0,
  has_type Phi Delta Gamma e (subst_ty .var_label (cons t' .var_ty) t) ->
  subtype Phi Delta t' t0 ->
  has_type Phi Delta Gamma (.pack t' e) (.ex t0 t)
| T_EExist : forall e e' t0 t t',
  has_type Phi Delta Gamma e (.all t0 t) ->
  has_type Phi (lift_delta (cons t0 Delta)) (cons t (lift_gamma_d Gamma)) e' (ren_ty id shift t') ->
  has_type Phi Delta Gamma (.unpack e e') t'
| T_ILUniv : forall cs lab e t,
  has_type (lift_phi ((cons (cs, lab)) Phi))
           (lift_delta_l Delta) (lift_gamma_l Gamma) e t ->
  has_type Phi Delta Gamma (.l_lam e) (.all_l cs lab t)
| T_ELUniv : forall cs lab lab' e t,
  (Phi |= (.condition cs lab lab')) ->
  has_type Phi Delta Gamma e (.all_l cs lab t) ->
  has_type Phi Delta Gamma (.lapp e lab') (subst_ty (cons lab' .var_label) .var_ty t)
| T_Sync : forall e pf,
  has_type Phi Delta Gamma e (.Data (adv pf)) ->
  has_type Phi Delta Gamma (.sync e) (.Data (adv pf))
| T_Sub : forall e t t',
  subtype Phi Delta t t' ->
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma e t'
| T_Annot : forall e t,
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma (.annot e t) t
-- NEED TO ADD IF STATEMENTS BACK (RELFLECTING NEW CORR DEFS)

theorem simple_var_typing :
  forall x Phi Delta (Gamma : gamma_context l d m),
     has_type Phi Delta Gamma (.var_tm x) (Gamma x) := by
  intro x Phi Delta Gamma
  exact has_type.T_Var x

theorem concrete_typing : @has_type 0 0 0 empty_phi empty_delta empty_gamma .skip .Unit :=
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
  check : has_type Phi Delta Gamma e exp

structure STType (Phi : phi_context l) (Delta : delta_context l d)
                     (t1 : ty l d) (t2 : ty l d) : Type where
  st : subtype Phi Delta t1 t2

notation:100  "grind" ck => (Conditional.side_condition_sound ck (by grind))

def check_subtype  (Phi : phi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : Option (Conditional (subtype Phi Delta t1 t2)) :=
    match t1, t2 with
    | x, .Any => .some ⟨True, fun _ => subtype.ST_Any x⟩
    | .Unit, .Unit => .some ⟨True, fun _ => subtype.ST_Unit⟩
    | .Data l1, .Data l2 => .some ⟨(Phi |= (.condition .leq l1 l2)), fun sc => subtype.ST_Data l1 l2 sc⟩
    | .var_ty x, t' =>
        .some ⟨subtype Phi Delta (Delta x) t',
               fun sub_proof => subtype.ST_Var x t' sub_proof⟩
    | .Public, .Data l1 =>
      .some ⟨True, fun _ => subtype.ST_RPublic l1⟩
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
                  | .none => ((t : ty l d) × Conditional (has_type Phi Delta Gamma e t))
                  | .some exp' => Conditional (has_type Phi Delta Gamma e exp')) :=
  match e with
  | .var_tm x =>
    match exp with
    | .none =>
        let proof := fun _ => has_type.T_Var x
        .some ⟨(Gamma x), ⟨True, proof⟩⟩
    | .some t =>
      let et1 := (Gamma x)
      let et2 := has_type.T_Var x
      let es := check_subtype Phi Delta (Gamma x) t
      match es with
      | .some es' =>
        .some ⟨es'.side_condition, fun sc => has_type.T_Sub (.var_tm x) et1 t (grind es') et2⟩
      | .none => .none
  | .skip =>
    match exp with
    | .none => .some ⟨.Unit, ⟨True, fun _ => has_type.T_IUnit⟩⟩
    | .some t =>
      match (check_subtype Phi Delta .Unit t) with
      | .some pf =>
        .some ⟨pf.side_condition,
              fun sc =>
                has_type.T_Sub .skip .Unit t (pf.side_condition_sound sc) has_type.T_IUnit⟩
      | .none => .none
  | .bitstring b =>
    match exp with
    | .none => .some ⟨.Public, ⟨True, fun _ => has_type.T_Const b⟩⟩
    | .some t =>
      match (check_subtype Phi Delta .Public t) with
      | .some pf =>
        .some ⟨pf.side_condition,
               fun sc => has_type.T_Sub (.bitstring b) .Public t (pf.side_condition_sound sc) (has_type.T_Const b)⟩
      | .none => .none
  | .Op op e1 e2 =>
    match exp with
    | .none => -- try to synthesize
      match infer Phi Delta Gamma e1 .none with -- find type of e1
      | .some ⟨.Data l1, pf1⟩ =>
        match infer Phi Delta Gamma e2 (.some (.Data l1)) with
        | .some e2pf =>
          .some ⟨.Data l1,
                 ⟨pf1.side_condition /\ e2pf.side_condition,
                  fun sc => has_type.T_Op op e1 e2 l1 (pf1.side_condition_sound (by grind)) (e2pf.side_condition_sound (by grind))⟩⟩
        | .none =>
          match infer Phi Delta Gamma e2 .none with  -- find type of e2
          | .some ⟨.Data l2, pf2⟩ =>
            match infer Phi Delta Gamma e1 (.some (.Data l2)) with
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
        match infer Phi Delta Gamma e1 (.some (.Data l)) with
        | .some pf1 =>
          match infer Phi Delta Gamma e2 (.some (.Data l)) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_Op op e1 e2 l (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .zero e =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
            .some ⟨.Public,
                   ⟨pf.side_condition, fun sc => has_type.T_Zero e l (pf.side_condition_sound (by grind))⟩⟩
      | _ => .none
    | .some t =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
        match check_subtype Phi Delta .Public t with
        | .some sub =>
          .some ⟨pf.side_condition /\ sub.side_condition,
                fun sc => has_type.T_Sub (.zero e) .Public t (sub.side_condition_sound (by grind)) (has_type.T_Zero e l (pf.side_condition_sound (by grind)))⟩
        | .none => .none
      | _ => .none
  | .if_tm e e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.Data l, cond_pf⟩ =>
        match infer Phi Delta Gamma e1 .none with
        | .some ⟨t1, pf1⟩ =>
          match infer Phi Delta Gamma e2 (.some t1) with
          | .some pf2 =>
            .some ⟨t1,
                  ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_If e e1 e2 l t1 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
          | .none =>
            match infer Phi Delta Gamma e2 .none with
            | .some ⟨t2, pf2⟩ =>
              match infer Phi Delta Gamma e1 (.some t2) with
              | .some pf1 =>
                .some ⟨t2, ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                       fun sc => has_type.T_If e e1 e2 l t2 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some t =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.Data l, cond_pf⟩ =>
        match infer Phi Delta Gamma e1 (.some t) with
        | .some pf1 =>
           match infer Phi Delta Gamma e2 (.some t) with
           | .some pf2 =>
             .some ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition ,
                    fun sc => has_type.T_If e e1 e2 l t (grind cond_pf) (grind pf1) (grind pf2)⟩
           | .none => .none
        | .none => .none
      | _ => .none
  | .alloc e =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨t, pf⟩ =>
        .some ⟨.Ref t, ⟨pf.side_condition, fun sc =>has_type.T_IRef e t (grind pf)⟩⟩
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .Ref t =>
        match infer Phi Delta Gamma e (.some t) with
        | .some pf => .some ⟨pf.side_condition, fun sc => has_type.T_IRef e t (grind pf)⟩
        | .none => .none
      | _ => .none
  | .dealloc e =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.Ref t, pf⟩ =>
        .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_ERef e t (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e (.some (.Ref exp_ty)) with
      | .some pf => .some ⟨pf.side_condition , fun sc => has_type.T_ERef e exp_ty (grind pf)⟩
      | .none => .none
  | .assign e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e1 .none with
      | .some ⟨.Ref t, pf1⟩ =>
        match infer Phi Delta Gamma e2 (.some t) with
        | .some pf2 =>
          .some ⟨.Unit, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_Assign e1 e2 t (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match exp_ty with
      | .Unit =>
        match infer Phi Delta Gamma e1 .none with
        | .some ⟨.Ref t, pf1⟩ =>
          match infer Phi Delta Gamma e2 (.some t) with
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
        match infer Phi Delta Gamma e (.some t1) with
        | .some pr => .some ⟨pr.side_condition, fun sc => has_type.T_ISumL e t1 t2 (grind pr)⟩
        | .none => .none
      | _ => .none
  | .inr e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort!
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer Phi Delta Gamma e (.some t2) with
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
        match infer Phi Delta extended_gamma e (.some t') with
        | .some pe => .some ⟨pe.side_condition, fun sc => has_type.T_IFun e t t' (grind pe)⟩
        | .none => .none
      | _ => .none
  | .app e1 e2 =>
    match exp with
    | .none => -- synthesize
      match infer Phi Delta Gamma e1 .none with
      | .some ⟨ty1, pf1⟩ =>
        match ty1 with
        | .arr t t' =>
          match infer Phi Delta Gamma e2 (.some t) with
          | .some pf2 => .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_EFun e1 e2 t t' (grind pf1) (grind pf2)⟩⟩
          | .none => .none
        | _ => .none
      | .none => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e1 .none with -- synthesize a type for e1
      | .some ⟨ty1, pf1⟩ =>
        match ty1 with
            | .arr t t' => -- correct type synthesized
              match infer Phi Delta Gamma e2 (some t) with -- check type of e2
              | .some pf2 =>
                let sub := check_subtype Phi Delta t' exp_ty -- check that t' is a subtype of exp_ty
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
      match infer Phi Delta Gamma e1 .none with
      | .some ⟨t1, pf1⟩ =>
        match infer Phi Delta Gamma e2 .none with
        | .some ⟨t2, pf2⟩ =>
          .some ⟨.prod t1 t2, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .prod t1 t2 =>
        match infer Phi Delta Gamma e1 (.some t1) with
        | .some pf1 =>
          match infer Phi Delta Gamma e2 (.some t2) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .left_tm e =>
    match exp with
    | .none => -- synthesize
      match infer Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t1, ⟨pf.side_condition, fun sc => has_type.T_EProdL e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype Phi Delta t1 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition ,
                 fun sc => has_type.T_Sub (.left_tm e) t1 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdL e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .right_tm e =>
    match exp with
    | .none => -- synthesize
      match infer Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t2, ⟨pf.side_condition, fun sc => has_type.T_EProdR e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype Phi Delta t2 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition,
                 fun sc => has_type.T_Sub (.right_tm e) t2 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdR e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .case e e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer Phi Delta (cons t1 Gamma) e1 .none with
        | .some ⟨t, pf2⟩ =>
          match infer Phi Delta (cons t2 Gamma) e2 (.some t) with
          | .some pf3 =>
            .some ⟨t, ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                       fun sc =>
                         has_type.T_ESum e t1 t2 t e1 e2 (grind pf1) (grind pf2) (grind pf3)⟩⟩
          | .none =>
            match infer Phi Delta (cons t2 Gamma) e2 .none with
            | .some ⟨t', pf2⟩ =>
              match infer Phi Delta (cons t1 Gamma) e1 (.some t') with
              | .some pf3 =>
                .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                            fun sc =>
                              has_type.T_ESum e t1 t2 t' e1 e2 (grind pf1) (grind pf3) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer Phi Delta (cons t1 Gamma) e1 (.some exp_ty) with
        | .some pf2 =>
          match infer Phi Delta (cons t2 Gamma) e2 (.some exp_ty) with
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
      match infer Phi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf1⟩ =>
        let sub := check_subtype Phi Delta t' t0
        match sub with
        | .some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
         .some ⟨result_ty,
                  ⟨pf1.side_condition /\ sub'.side_condition,
                  fun sc => has_type.T_EUniv t t' t0 e (grind sub') (grind pf1)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer Phi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf⟩ =>
        let sub := check_subtype Phi Delta t' t0
        match sub with
        | some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
          let sub_result := check_subtype Phi Delta result_ty exp_ty
          match sub_result with
          | .some sub_result' =>
            .some ⟨pf.side_condition /\ sub'.side_condition /\ sub_result'.side_condition,
                      fun sc =>
                        has_type.T_Sub (.tapp e t') result_ty exp_ty (grind sub_result')
                          (has_type.T_EUniv t t' t0 e (grind sub') (grind pf))⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .annot e t =>
    match exp with
    | .none => -- synthesize a type
      match infer Phi Delta Gamma e (.some t) with
      | .some pf => .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_Annot e t (grind pf)⟩⟩
      | .none => .none
    | .some exp_ty => -- check the type of annotation
      match check_subtype Phi Delta t exp_ty with -- first check for subtype
      | .some sub =>
        match infer Phi Delta Gamma e (.some t) with -- check that e has type t
        | .some pf =>
          .some ⟨sub.side_condition /\ pf.side_condition, fun sc => has_type.T_Sub (.annot e t) t exp_ty (grind sub) (has_type.T_Annot e t (grind pf))⟩
        | .none => .none
      | .none => .none
  | _ =>
    match exp with
    | .some _ => .none
    | .none => .none

syntax "tc" term:max term:max term:max term:max term:max tactic:max : tactic

macro_rules
  | `(tactic| tc $Phi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Delta $Gamma $e (some $t) with
      | some result =>
          dsimp [infer, check_subtype, cons] at h;
          cases result with
          | mk side_condition side_condition_sound =>
            cases h;
            apply side_condition_sound
            $k
      | none =>
          dsimp [infer, check_subtype] at h
          cases h
    )

#reduce infer empty_phi empty_delta empty_gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.some (.arr .Unit .Unit))

#reduce infer empty_phi empty_delta (cons .Unit empty_gamma) (.var_tm ⟨0, by omega⟩) (.some .Unit)

theorem skip_has_unit_type (Phi : phi_context l) (Delta : delta_context l d)
                           (Gamma : gamma_context l d m) :
                           has_type Phi Delta Gamma .skip .Any := by
  cases h : infer Phi Delta Gamma .skip (.some .Any) with
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

theorem lambda_simple (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type Phi Delta Gamma (.fixlam (.alloc .skip)) (.arr .Unit (.Ref .Unit)) := by
  tc Phi Delta Gamma (.fixlam (.alloc .skip)) (.arr .Unit (.Ref .Unit)) (try grind)

theorem lambda_identity_unit (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type Phi Delta Gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.arr .Unit .Unit) := by
  tc Phi Delta Gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.arr .Unit .Unit) (try grind)

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
                                has_type Phi Delta Gamma (.bitstring b) (.Data (.latl l1)) := by
  tc Phi Delta Gamma (.bitstring b) (.Data (.latl l1)) (try simp)

-- Test theorem for inl with skip
theorem inl_skip_has_sum_type (Phi : phi_context l) (Delta : delta_context l d)
                              (Gamma : gamma_context l d m) (t2 : ty l d) :
                              has_type Phi Delta Gamma (.inl .skip) (.sum .Unit t2) := by
  tc Phi Delta Gamma (.inl .skip) (.sum .Unit t2) (try grind)

theorem fixlam_identity (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type Phi Delta Gamma
                          (.fixlam .skip)
                          (.arr .Any .Unit) := by
  tc Phi Delta Gamma (.fixlam .skip) (.arr .Any .Unit) (try grind)

theorem pair_easy (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type Phi Delta Gamma
                        (.tm_pair .skip .skip)
                        (.prod .Unit .Unit) := by
  tc Phi Delta Gamma (.tm_pair .skip .skip) (.prod .Unit .Unit) (try grind)
