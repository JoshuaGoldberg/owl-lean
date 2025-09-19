import OwlLean.OwlLang.Owl

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

def gamma_context (l : Nat) (d : Nat) (m : Nat) := Fin m -> ty l d
def delta_context (l : Nat) (d : Nat) := Fin d -> ty l d
def phi_context (l : Nat) := (List (constr l))

def empty_gamma : gamma_context l d 0 :=
  fun (i : Fin 0) => nomatch i

def empty_delta : delta_context l 0 :=
  fun (i : Fin 0) => nomatch i

def empty_phi : (phi_context l) := []

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

def phi_map_holds (l : Nat) (pm : phi_map l) (co : constr l) : Prop :=
  match co with
  | (.condition c l1 l2) => (valid_constraint (.condition c (subst_label pm l1) (subst_label pm l2)))

def lift_phi (pm : phi_context l) : phi_context (l + 1) :=
  .map (ren_constr shift) pm

inductive valid_phi_map : forall l, phi_map l -> phi_context l -> Prop where
| phi_empty_valid : forall (pm : phi_map 1),
  valid_phi_map 1 pm empty_phi
| phi_constraint_valid : forall l pm phictx c,
  valid_phi_map l pm phictx ->
  phi_map_holds l pm c ->
  valid_phi_map l pm (c :: phictx)
| phi_var_holds : forall l lab pm phictx,
  valid_phi_map l pm phictx ->
  valid_phi_map (l + 1) (cons lab pm) (lift_phi phictx)

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
    (((.condition cs (.var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi))
    |= (.condition cs (.var_label var_zero) (ren_label shift lab'))) ->
    subtype ((.condition cs (.var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi)) (lift_delta_l Delta) t t' ->
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
  | ST_Lem : forall co t t',
    subtype (co :: Phi) Delta t t' ->
    subtype ((negate_cond co) :: Phi) Delta t t' ->
    subtype Phi Delta t t'

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
  has_type Phi Delta Gamma (.bitstring b) (.Data (.latl L.bot))
| T_Op : forall op e1 e2 l,
  has_type Phi Delta Gamma e1 (.Data l) ->
  has_type Phi Delta Gamma e2 (.Data l) ->
  has_type Phi Delta Gamma (.Op op e1 e2) (.Data l)
| T_Zero : forall e l,
  has_type Phi Delta Gamma e (.Data l) ->
  has_type Phi Delta Gamma (.zero e) (.Data (.latl (L.bot)))
| T_If : forall e e1 e2 t,
  has_type Phi Delta Gamma e (.Data (.latl L.bot)) ->
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
| T_EUniv {Phi Delta Gamma} : forall t t' t0 e,
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
  has_type ((.condition cs (.var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi))
                                        (lift_delta_l Delta) (lift_gamma_l Gamma) e t ->
  has_type Phi Delta Gamma (.l_lam e) (.all_l cs lab t)
| T_ELUniv : forall cs lab lab' e t,
  (Phi |= (.condition cs lab lab')) ->
  has_type Phi Delta Gamma e (.all_l cs lab t) ->
  has_type Phi Delta Gamma (.lapp e lab') (subst_ty (cons lab' .var_label) .var_ty t)
| T_Lem : forall co e t,
  has_type (co :: Phi) Delta Gamma e t ->
  has_type ((negate_cond co) :: Phi) Delta Gamma e t ->
  has_type Phi Delta Gamma e t
| T_LIf : forall co e1 e2 t,
  has_type (co :: Phi) Delta Gamma e1 t ->
  has_type (co :: Phi) Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.if_c co e1 e2) t
| T_Sync : forall e pf,
  has_type Phi Delta Gamma e (.Data (adv pf)) ->
  has_type Phi Delta Gamma (.sync e) (.Data (adv pf))
| T_Sub : forall e t t',
  subtype Phi Delta t t' ->
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma e t'

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

structure CheckType (Phi : phi_context l) (Delta : delta_context l d)
                     (Gamma : gamma_context l d m) (e : tm l d m) (exp : ty l d) : Type where
  check : has_type Phi Delta Gamma e exp

structure STType (Phi : phi_context l) (Delta : delta_context l d)
                     (t1 : ty l d) (t2 : ty l d) : Type where
  st : subtype Phi Delta t1 t2


def check_subtype  (Phi : phi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : Option (STType Phi Delta t1 t2) :=
    .none

def infer (Phi : phi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          Option (match exp with
                  | .none => ((t : ty l d) × CheckType Phi Delta Gamma e t)
                  | .some exp' => (CheckType Phi Delta Gamma e exp')) :=
  match e with
  | .var_tm x =>
    match exp with
    | .none => .some ⟨(Gamma x), { check := has_type.T_Var x}⟩
    | .some t =>
      let et1 := (Gamma x)
      let et2 := has_type.T_Var x
      let es := check_subtype Phi Delta et1 t
      match es with
      | .some es' =>
        .some { check := has_type.T_Sub (.var_tm x) et1 t es'.st et2 }
      | .none => .none
  | .skip =>
    match exp with
    | .none => .some ⟨.Unit, { check := has_type.T_IUnit }⟩
    | .some t =>
      match t with
      | .Unit => .some { check :=  has_type.T_IUnit }
      | _ => .none
  | .bitstring b =>
    match exp with
    | .none => .some ⟨.Data (.latl SecurityLevel.pub), { check := has_type.T_Const b }⟩
    | .some t =>
      match t with
      | .Data (.latl SecurityLevel.pub) => .some { check := has_type.T_Const b }
      | _ => .none
  | .Op op e1 e2 =>
    match exp with
    | .none => -- try to synthesize
      match infer Phi Delta Gamma e1 .none with -- find type of e1
      | .some ⟨.Data l1, pf1⟩ =>
        match infer Phi Delta Gamma e2 .none with  -- find type of e2 -- the join
        | .some ⟨.Data l2, pf2⟩ =>
            match check_subtype Phi Delta (.Data l2) (.Data l1) with -- check if e2 <: e1
            | .some sub_pf =>
              let pf2_sub := has_type.T_Sub e2 (.Data l2) (.Data l1) sub_pf.st pf2.check
              .some ⟨.Data l1, { check := has_type.T_Op op e1 e2 l1 pf1.check pf2_sub }⟩
            | .none =>
              match check_subtype Phi Delta (.Data l1) (.Data l2) with -- check if e1 <: e2
              | .some sub_pf =>
                let pf1_sub := has_type.T_Sub e1 (.Data l1) (.Data l2) sub_pf.st pf1.check
                .some ⟨.Data l2, { check := has_type.T_Op op e1 e2 l2 pf1_sub pf2.check }⟩
              | .none => .none
        | .some _ => .none
        | .none => .none
      | .some _ => .none
      | .none => .none
    | .some t =>
      match t with
      | .Data l =>
        match infer Phi Delta Gamma e1 (.some (.Data l)) with
        | .some pf1 =>
          match infer Phi Delta Gamma e2 (.some (.Data l)) with
          | .some pf2 => .some { check := has_type.T_Op op e1 e2 l pf1.check pf2.check }
          | .none => .none
        | .none => .none
      | _ => .none
  | .inl e =>
    match exp with
    | .none => .none
    | .some t =>
      match t with
      | .sum t1 t2 =>
        let epf := infer Phi Delta Gamma e (.some t1)
        match epf with
        | .some pr => .some { check :=  has_type.T_ISumL e t1 t2 pr.check }
        | .none => .none
      | _ => .none
  | .fixlam e =>
    match exp with
    | .none => .none -- TODO, allow synthesis
    | .some t =>
      match t with
      | .arr t t' =>
        let extended_gamma := cons (.arr t t') (cons t Gamma)
        let pe := infer Phi Delta extended_gamma e (.some t')
        match pe with
        | .some pe' => .some { check :=  has_type.T_IFun e t t' pe'.check }
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
          | .some pf2 => .some ⟨t', { check := has_type.T_EFun e1 e2 t t' pf1.check pf2.check }⟩
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
                    let app_proof := has_type.T_EFun e1 e2 t t' pf1.check pf2.check -- proof that |- e1 e2 : t'
                    .some { check := has_type.T_Sub (.app e1 e2) t' exp_ty sub'.st app_proof } -- proof that |- e1 e2 : exp_ty
                | .none => .none
              | .none => .none
            | _ => .none
      | .none => .none
  | _ =>
    match exp with
    | .some _ => .none
    | .none => .none

syntax "tc" term:max term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| tc $Phi:term $Delta:term $Gamma:term $e:term $t:term) => `(tactic|
      cases h : infer $Phi $Delta $Gamma $e (some $t) with
      | some result => exact result.check
      | none => simp [infer] at h)

theorem skip_has_unit_type (Phi : phi_context l) (Delta : delta_context l d)
                           (Gamma : gamma_context l d m) :
                           has_type Phi Delta Gamma .skip .Unit := by
  tc Phi Delta Gamma .skip .Unit

theorem bitstring_has_bot_type (Phi : phi_context l) (Delta : delta_context l d)
                                (Gamma : gamma_context l d m) (b : binary) :
                                has_type Phi Delta Gamma (.bitstring b) (.Data (.latl L.bot)) := by
  tc Phi Delta Gamma (.bitstring b) (.Data (.latl SecurityLevel.pub))

-- Test theorem for inl with skip
theorem inl_skip_has_sum_type (Phi : phi_context l) (Delta : delta_context l d)
                              (Gamma : gamma_context l d m) (t2 : ty l d) :
                              has_type Phi Delta Gamma (.inl .skip) (.sum .Unit t2) := by
  tc Phi Delta Gamma (.inl .skip) (.sum .Unit t2)

theorem fixlam_identity (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type Phi Delta Gamma
                          (.fixlam .skip)
                          (.arr .Any .Unit) := by
  tc Phi Delta Gamma (.fixlam .skip) (.arr .Any .Unit)

mutual
-- Synthesis rules (infer type from term structure)
inductive synth : (Phi : phi_context l) → (Delta : delta_context l d) →
                  (Gamma : gamma_context l d m) → tm l d m → ty l d → Prop where
| S_Var : synth Phi Delta Gamma (.var_tm x) (Gamma x)
| S_Unit : synth Phi Delta Gamma .skip .Unit
| S_Const : synth Phi Delta Gamma (.bitstring b) (.Data (.latl L.bot))
| S_App : synth Phi Delta Gamma e1 (.arr t t') →
          check Phi Delta Gamma e2 t →
          synth Phi Delta Gamma (.app e1 e2) t'
| S_Deref : synth Phi Delta Gamma e (.Ref t) →
            synth Phi Delta Gamma (!e) t
| S_ProjL : synth Phi Delta Gamma e (.prod t1 t2) →
            synth Phi Delta Gamma (.left_tm e) t1
| S_ProjR : synth Phi Delta Gamma e (.prod t1 t2) →
            synth Phi Delta Gamma (.right_tm e) t2
| S_Case : synth Phi Delta Gamma e (.sum t1 t2) →
           check Phi Delta (cons t1 Gamma) e1 t →
           check Phi Delta (cons t2 Gamma) e2 t →
           synth Phi Delta Gamma (.case e e1 e2) t
| S_TApp : synth Phi Delta Gamma e (.all t0 t) →
           subtype Phi Delta t' t0 →
           synth Phi Delta Gamma (.tapp e t') (subst_ty .var_label (cons t' .var_ty) t)
| S_LApp : synth Phi Delta Gamma e (.all_l cs lab t) →
           (Phi |= (.condition cs lab lab')) →
           synth Phi Delta Gamma (.lapp e lab') (subst_ty (cons lab' .var_label) .var_ty t)
| S_Unpack : synth Phi Delta Gamma e (.ex t0 t) →
             check Phi (lift_delta (cons t0 Delta)) (cons t (lift_gamma_d Gamma)) e' (ren_ty id shift t') →
             synth Phi Delta Gamma (.unpack e e') t'
| S_Op : check Phi Delta Gamma e1 (.Data l) →
         check Phi Delta Gamma e2 (.Data l) →
         synth Phi Delta Gamma (.Op f e1 e2) (.Data l)
| S_Zero : synth Phi Delta Gamma e (.Data l) →
           synth Phi Delta Gamma (.zero e) (.Data (.latl L.bot))
| S_If : check Phi Delta Gamma e (.Data (.latl L.bot)) →
         check Phi Delta Gamma e1 t →
         check Phi Delta Gamma e2 t →
         synth Phi Delta Gamma (.if_tm e e1 e2) t
| S_Assign : synth Phi Delta Gamma e1 (.Ref t) →
             check Phi Delta Gamma e2 t →
             synth Phi Delta Gamma (.assign e1 e2) .Unit
| S_Sync : synth Phi Delta Gamma e (.Data (adv pf)) →
           synth Phi Delta Gamma (.sync e) (.Data (adv pf))
| S_Pair : synth Phi Delta Gamma e1 t1 →
           synth Phi Delta Gamma e2 t2 →
           synth Phi Delta Gamma (.tm_pair e1 e2) (.prod t1 t2)
| S_Annot : check Phi Delta Gamma e t ->
            synth Phi Delta Gamma (.annot e t) t
| S_Alloc : synth Phi Delta Gamma e t →
            synth Phi Delta Gamma (.alloc e) (.Ref t)
| S_IfC : synth (co :: Phi) Delta Gamma e1 t →
          synth ((negate_cond co) :: Phi) Delta Gamma e2 t →
          synth Phi Delta Gamma (.if_c co e1 e2) t
| S_Lem : synth (co :: Phi) Delta Gamma e t →
          synth ((negate_cond co) :: Phi) Delta Gamma e t →
          synth Phi Delta Gamma e t

-- Checking rules (verify term has expected type)
inductive check : (Phi : phi_context l) → (Delta : delta_context l d) →
                  (Gamma : gamma_context l d m) → tm l d m → ty l d → Prop where
| C_Lam : check Phi Delta (cons (.arr t t') (cons t Gamma)) e t' →
          check Phi Delta Gamma (.fixlam e) (.arr t t')
| C_Inl : check Phi Delta Gamma e t1 →
          check Phi Delta Gamma (.inl e) (.sum t1 t2)
| C_Inr : check Phi Delta Gamma e t2 →
          check Phi Delta Gamma (.inr e) (.sum t1 t2)
| C_Pack : check Phi Delta Gamma e (subst_ty .var_label (cons t' .var_ty) t) →
           subtype Phi Delta t' t0 →
           check Phi Delta Gamma (.pack t' e) (.ex t0 t)
| C_TLam : check Phi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e t →
           check Phi Delta Gamma (.tlam e) (.all t0 t)
| C_LLam : check ((.condition cs (.var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi))
                 (lift_delta_l Delta) (lift_gamma_l Gamma) e t →
           check Phi Delta Gamma (.l_lam e) (.all_l cs lab t)
| C_Lem : check (co :: Phi) Delta Gamma e t →
          check ((negate_cond co) :: Phi) Delta Gamma e t →
          check Phi Delta Gamma e t
| C_Sub : synth Phi Delta Gamma e t →
          subtype Phi Delta t t' →
          check Phi Delta Gamma e t'
end
