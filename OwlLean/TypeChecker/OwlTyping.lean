import OwlLean.OwlLang.Owl
open Owl

-- sanity checks
#check (tm.error : tm 0 0)
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

def lift_gamma (Gamma : gamma_context l d m)
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
inductive is_value : tm l m -> Prop where
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
| pack_value : forall v,
  is_value v ->
  is_value (.pack v)

-- subtyping rules for Owl
inductive subtype : (phi_context l) -> (delta_context l d) ->
    ty l d -> ty l d -> Prop where
| ST_Var : forall x t',
  subtype Phi Delta (Delta x) t' ->
  subtype Phi Delta (.var_ty x) t'
| ST_Any : forall t,
  subtype Phi Delta t Any
| ST_Unit : subtype Phi Delta .Unit .Unit
| ST_Data : forall lab (lab' : label l),
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
| ST_LatUniv : forall cs (lab : label l) (lab' : label l) t t',
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
  tm l m -> ty l d -> Prop where
| T_Var : forall x,
  has_type Phi Delta Gamma (.var_tm x) (Gamma x)
| T_IUnit : has_type Phi Delta Gamma .skip .Unit
| T_Const : forall b,
  has_type Phi Delta Gamma (.bitstring b) (.Data (.latl L.bot))
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
  has_type Phi Delta (cons t (cons (.arr t t') Gamma)) e t ->
  has_type Phi Delta Gamma (.fixlam e) (.arr t t')
| T_EFun : forall e1 e2 t t',
  has_type Phi Delta Gamma e1 (.arr t t') ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (.app e1 e2) t
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
  has_type Phi (lift_delta (cons t0 Delta)) (lift_gamma Gamma) e t ->
  has_type Phi Delta Gamma (.tlam e) (.all t0 t)
| T_EUniv : forall t t' t0 e,
  subtype Phi Delta t' t0 ->
  has_type Phi Delta Gamma e (.all t0 t) ->
  has_type Phi Delta Gamma (.tapp e) (subst_ty .var_label (cons t' var_ty) t)
| T_IExist : forall e t t' t0,
  has_type Phi Delta Gamma e (subst_ty .var_label (cons t' .var_ty) t) ->
  subtype Phi Delta t' t0 ->
  has_type Phi Delta Gamma (.pack e) (.ex t0 t)
| T_EExist : forall e e' t0 t t',
  has_type Phi Delta Gamma e (.all t0 t) ->
  has_type Phi (lift_delta (cons t0 Delta)) (cons t (lift_gamma Gamma)) e' (ren_ty id shift t') ->
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

theorem simple_var_typing
       (x : Fin m) : has_type Phi Delta Gamma (.var_tm x) (Gamma x) :=
  has_type.T_Var x

theorem concrete_typing : @has_type 0 0 0 empty_phi empty_delta empty_gamma .skip .Unit :=
  has_type.T_IUnit
