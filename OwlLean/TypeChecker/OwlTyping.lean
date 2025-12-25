import OwlLean.OwlLang.Owl
import Lean

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

@[simp]
def gamma_context (l : Nat) (d : Nat) (m : Nat) := Fin m -> ty l d
@[simp]
def delta_context (l : Nat) (d : Nat) := Fin d -> ty l d
@[simp]
def phi_context (l : Nat) := Fin l -> (cond_sym × label l)

@[simp]
def empty_gamma : gamma_context l d 0 :=
  fun (i : Fin 0) => nomatch i

@[simp]
def empty_delta : delta_context l 0 :=
  fun (i : Fin 0) => nomatch i

@[simp]
def empty_phi : (phi_context 0) :=
  fun (i : Fin 0) => nomatch i

@[simp]
def lift_delta (Delta : Fin (d + 1) -> ty l d)
  : delta_context l (d + 1)
  := fun i => ren_ty id shift (Delta i)

@[simp]
def lift_delta_l (Delta : delta_context l d)
  : delta_context (l + 1) d
  := fun i => ren_ty shift id (Delta i)

@[simp]
def lift_gamma_d (Gamma : gamma_context l d m)
  : gamma_context l (d + 1) m
  := fun i => ren_ty id shift (Gamma i)

@[simp]
def lift_gamma_l (Gamma : gamma_context l d m)
  : gamma_context (l + 1) d m
  := fun i => ren_ty shift id (Gamma i)

-- Convert from labels down to lattice elements
@[simp]
def interp_lattice (l : label 0) : L.labels :=
  match l with
  | .latl x => x
  | .ljoin x y => (L.join (interp_lattice x) (interp_lattice y))
  | .lmeet x y => (L.meet (interp_lattice x) (interp_lattice y))
  | .var_label n => nomatch n
  | .default => L.bot

@[simp]
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
@[simp]
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


@[simp]
def phi_map (l : Nat) : Type := (Fin l) -> (label 0)
@[simp]
def empty_phi_map : phi_map 0 := fun (i : Fin 0) => nomatch i

@[simp]
def phi_map_holds (l : Nat) (pm : phi_map l) (co : constr l) : Prop :=
  match co with
  | (.condition c l1 l2) => (valid_constraint (.condition c (subst_label pm l1) (subst_label pm l2)))

@[simp]
def lift_phi (pm : Fin (l + 1) -> (cond_sym × label l)) : phi_context (l + 1) :=
  fun i =>
    let ⟨sym, lab⟩ := (pm i)
    ⟨sym, ren_label shift lab⟩

@[simp]
def pcons (x : cond_sym × label l) (phi : phi_context l) : phi_context (l + 1) :=
  (lift_phi (cons x phi))

@[simp]
def dcons (x : ty l d) (delta : delta_context l d) : delta_context l (d+1) :=
  (lift_delta (cons x delta))

@[simp]
def phi_map.valid (p : phi_map l) (c : phi_context l) :=
  Fin.foldr l (fun i acc =>
    acc ∧ (let (s, l) := c i; valid_constraint (.condition s (p i) (subst_label p l)))
  ) True

def Fin.forall_fold {l} (f : Fin l -> Prop) :
  (forall i, f i) =
  Fin.foldr l (fun i acc =>
    acc ∧ f i
  ) True := by
    ext
    constructor
    {
      intros h
      induction l
      simp
      simp [Fin.foldr_succ]
      simp [h 0]
      rename_i ih
      apply ih
      grind
    }
    {
      intros h
      intros i
      induction l
      cases i; omega
      apply Fin.cases
      rename_i ih
      simp [Fin.foldr_succ] at h
      grind
      intros j
      rename_i ih
      specialize (ih (fun x => f x.succ))
      apply ih
      simp [Fin.foldr_succ] at h
      grind
    }


@[simp]
def phi_entails_c (pctx : phi_context l) (co : constr l) : Prop :=
  (forall pm,
    pm.valid pctx ->
    phi_map_holds l pm co)

structure CorruptionSet where
  is_corrupt : label 0 -> Prop
  has_bot : is_corrupt (label.latl L.bot)
  downward_closed : forall l l',
                    is_corrupt l' ->
                    L.leq (interp_lattice l) (interp_lattice l') = true ->
                    is_corrupt l


@[grind]
theorem CorruptionSet.by_downwards_closed (C : CorruptionSet) :
  C.is_corrupt l ->
  Owl.L.leq (interp_lattice l') (interp_lattice l) = true ->
  C.is_corrupt l' := by
    intros h1 h2
    apply C.downward_closed
    apply h1
    assumption

@[simp]
def psi_context (l : Nat) := (List (corruption l))

@[simp]
def empty_psi (l : Nat) : psi_context l := []

@[simp]
def lift_psi (pm : psi_context l) : psi_context (l + 1) :=
  pm.map (ren_corruption shift)

@[simp]
def subst_psi_context (sigma_label : Fin m_label -> label n_label)
  (psi : psi_context m_label) : psi_context n_label :=
  psi.map (subst_corruption sigma_label)

@[simp]
def C_satisfies_psi (C : CorruptionSet) (psi : psi_context 0) : Prop :=
  List.foldr (fun i acc =>
    acc ∧ match i with
    | corruption.corr x => C.is_corrupt x
    | .not_corr x => ¬ (C.is_corrupt x)
  ) True psi

@[simp]
def  phi_psi_entail_corr (phictx : phi_context l) (psictx : psi_context l) (co : corruption l) : Prop :=
  (forall (pm : phi_map l) C,
    (pm.valid phictx) ->
    (C_satisfies_psi C (subst_psi_context pm psictx)) ->
    (C_satisfies_psi C (subst_psi_context pm [co])))

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
  inductive subtype : (phi_context l) -> (psi_context l) -> (delta_context l d) ->
      ty l d -> ty l d -> Prop where
  | ST_Var : forall x t',
    subtype Phi Psi Delta (Delta x) t' ->
    subtype Phi Psi Delta (.var_ty x) t'
  | ST_Any : forall t,
    subtype Phi Psi Delta t .Any
  | ST_Unit : subtype Phi Psi Delta .Unit .Unit
  | ST_Data : forall lab lab',
    (Phi |= (.condition .leq lab lab')) ->
    subtype Phi Psi Delta (.Data lab) (.Data lab')
  | ST_RPublic : forall lab,
    subtype Phi Psi Delta .Public (.Data lab)
  | ST_LPublic {Phi Psi Delta} : forall lab,
     phi_psi_entail_corr Phi Psi (.corr lab) ->
    subtype Phi Psi Delta (.Data lab) .Public
  | ST_Func : forall t1' t1 t2 t2',
    subtype Phi Psi Delta t1' t1 ->
    subtype Phi Psi Delta t2 t2' ->
    subtype Phi Psi Delta (.arr t1 t2) (.arr t1' t2')
  | ST_Prod : forall t1 t1' t2 t2',
    subtype Phi Psi Delta t1 t1' ->
    subtype Phi Psi Delta t2 t2' ->
    subtype Phi Psi Delta (.prod t1 t2) (.prod t1' t2')
  | ST_Sum : forall t1 t1' t2 t2',
    subtype Phi Psi Delta t1 t1' ->
    subtype Phi Psi Delta t2 t2' ->
    subtype Phi Psi Delta (.sum t1 t2) (.sum t1' t2')
  | ST_Ref : forall t,
    subtype Phi Psi Delta (.Ref t) (.Ref t)
  | ST_Univ : forall t0 t0' t t',
    subtype Phi Psi Delta t0 t0' ->
    subtype Phi Psi (lift_delta (cons t0' Delta)) t t' ->
    subtype Phi Psi Delta (.all t0 t) (.all t0' t')
  | ST_Exist : forall t0 t0' t t',
    subtype Phi Psi Delta t0 t0' ->
    subtype Phi Psi (lift_delta (cons t0 Delta)) t t' ->
    subtype Phi Psi Delta (.ex t0 t) (.ex t0' t')
  | ST_LatUniv : forall cs lab lab' t t',
    ((lift_phi (cons (cs, lab) Phi))
    |= (.condition cs (.var_label var_zero) (ren_label shift lab'))) ->
    subtype (lift_phi (cons (cs, lab) Phi)) (lift_psi Psi) (lift_delta_l Delta) t t' ->
    subtype Phi Psi Delta (.all_l cs lab t) (.all_l cs lab' t')
  | ST_LIf1 : forall lab t1 t2 t1',
    phi_psi_entail_corr Phi Psi (.corr lab) ->
    subtype Phi Psi Delta t1 t1' ->
    subtype Phi Psi Delta (.t_if lab t1 t2) t1'
  | ST_LIf2 : forall lab t1 t2 t2',
    phi_psi_entail_corr Phi Psi (.not_corr lab) ->
    subtype Phi Psi Delta t2 t2' ->
    subtype Phi Psi Delta (.t_if lab t1 t2) t2'
  | ST_RIf1 : forall lab t1 t1' t2',
    phi_psi_entail_corr Phi Psi (.corr lab) ->
    subtype Phi Psi Delta t1 t1' ->
    subtype Phi Psi Delta t1 (.t_if lab t1' t2')
  | ST_RIf2 : forall lab t2 t1' t2',
    phi_psi_entail_corr Phi Psi (.not_corr lab) ->
    subtype Phi Psi Delta t2 t2' ->
    subtype Phi Psi Delta t2 (.t_if lab t1' t2')
  | ST_Corr : forall lab t1 t2,
    subtype Phi ((.corr lab) :: Psi) Delta t1 t2 ->
    subtype Phi ((.not_corr lab) :: Psi) Delta t1 t2 ->
    subtype Phi Psi Delta t1 t2
  | ST_Refl : forall x,
    subtype Phi Psi Delta x x

-- Typing rules for Owl
inductive has_type : (Phi : phi_context l) -> (Psi : psi_context l) -> (Delta : delta_context l d) -> (Gamma : gamma_context l d m) ->
  tm l d m -> ty l d -> Prop where
| T_Var : forall x,
  has_type Phi Psi Delta Gamma (.var_tm x) (Gamma x)
| T_IUnit : has_type Phi Psi Delta Gamma .skip .Unit
| T_Const : forall b,
  has_type Phi Psi Delta Gamma (.bitstring b) .Public
| T_Op : forall op e1 e2 l,
  has_type Phi Psi Delta Gamma e1 (.Data l) ->
  has_type Phi Psi Delta Gamma e2 (.Data l) ->
  has_type Phi Psi Delta Gamma (.Op op e1 e2) (.Data l)
| T_Zero : forall e l,
  has_type Phi Psi Delta Gamma e (.Data l) ->
  has_type Phi Psi Delta Gamma (.zero e) .Public
| T_If {Phi Psi Delta Gamma} : forall e e1 e2 t,
  has_type Phi Psi Delta Gamma e .Public ->
  has_type Phi Psi Delta Gamma e1 t ->
  has_type Phi Psi Delta Gamma e2 t ->
  has_type Phi Psi Delta Gamma (.if_tm e e1 e2) t
| T_IRef : forall e t,
  has_type Phi Psi Delta Gamma e t ->
  has_type Phi Psi Delta Gamma (.alloc e) (.Ref t)
| T_ERef : forall e t,
  has_type Phi Psi Delta Gamma e (.Ref t) ->
  has_type Phi Psi Delta Gamma (! e) t
| T_Assign : forall e1 e2 t,
  has_type Phi Psi Delta Gamma e1 (.Ref t) ->
  has_type Phi Psi Delta Gamma e2 t ->
  has_type Phi Psi Delta Gamma (.assign e1 e2) .Unit
| T_IFun : forall e t t',
  has_type Phi Psi Delta (cons (.arr t t') (cons t Gamma)) e t' ->
  has_type Phi Psi Delta Gamma (.fixlam e) (.arr t t')
| T_EFun : forall e1 e2 t t',
  has_type Phi Psi Delta Gamma e1 (.arr t t') ->
  has_type Phi Psi Delta Gamma e2 t ->
  has_type Phi Psi Delta Gamma (.app e1 e2) t'
| T_IProd : forall e1 e2 t1 t2,
  has_type Phi Psi Delta Gamma e1 t1 ->
  has_type Phi Psi Delta Gamma e2 t2 ->
  has_type Phi Psi Delta Gamma (.tm_pair e1 e2) (.prod t1 t2)
| T_EProdL : forall e t1 t2,
  has_type Phi Psi Delta Gamma e (.prod t1 t2) ->
  has_type Phi Psi Delta Gamma (.left_tm e) t1
| T_EProdR : forall e t1 t2,
  has_type Phi Psi Delta Gamma e (.prod t1 t2) ->
  has_type Phi Psi Delta Gamma (.right_tm e) t2
| T_ISumL : forall e t1 t2,
  has_type Phi Psi Delta Gamma e t1 ->
  has_type Phi Psi Delta Gamma (.inl e) (.sum t1 t2)
| T_ISumR : forall e t1 t2,
  has_type Phi Psi Delta Gamma e t2 ->
  has_type Phi Psi Delta Gamma (.inr e) (.sum t1 t2)
| T_ESum : forall e t1 t2 t e1 e2,
  has_type Phi Psi Delta Gamma e (.sum t1 t2) ->
  has_type Phi Psi Delta (cons t1 Gamma) e1 t ->
  has_type Phi Psi Delta (cons t2 Gamma) e2 t ->
  has_type Phi Psi Delta Gamma (.case e e1 e2) t
| T_IUniv : forall t0 t e,
  has_type Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e t ->
  has_type Phi Psi Delta Gamma (.tlam e) (.all t0 t)
| T_EUniv : forall t t' t0 e,
  subtype Phi Psi Delta t' t0 ->
  has_type Phi Psi Delta Gamma e (.all t0 t) ->
  has_type Phi Psi Delta Gamma (.tapp e t') (subst_ty .var_label (cons t' .var_ty) t)
| T_IExist : forall e t t' t0,
  has_type Phi Psi Delta Gamma e (subst_ty .var_label (cons t' .var_ty) t) ->
  subtype Phi Psi Delta t' t0 ->
  has_type Phi Psi Delta Gamma (.pack t' e) (.ex t0 t)
| T_EExist : forall e e' t0 t t',
  has_type Phi Psi Delta Gamma e (.ex t0 t) ->
  has_type Phi Psi (lift_delta (cons t0 Delta)) (cons t (lift_gamma_d Gamma)) e' (ren_ty id shift t') ->
  has_type Phi Psi Delta Gamma (.unpack e e') t'
| T_ILUniv : forall cs lab e t,
  has_type (lift_phi ((cons (cs, lab)) Phi))
           (lift_psi Psi) (lift_delta_l Delta) (lift_gamma_l Gamma) e t ->
  has_type Phi Psi Delta Gamma (.l_lam e) (.all_l cs lab t)
| T_ELUniv : forall cs lab lab' e t,
  (Phi |= (.condition cs lab lab')) ->
  has_type Phi Psi Delta Gamma e (.all_l cs lab t) ->
  has_type Phi Psi Delta Gamma (.lapp e lab') (subst_ty (cons lab' .var_label) .var_ty t)
| T_Sync : forall e,
  has_type Phi Psi Delta Gamma e .Public ->
  has_type Phi Psi Delta Gamma (.sync e) .Public
| T_IfCorr1 : forall lab t e1 e2,
  (phi_psi_entail_corr Phi Psi (.not_corr lab)) ->
  has_type Phi Psi Delta Gamma e2 t ->
  has_type Phi Psi Delta Gamma (.if_c lab e1 e2) t
| T_IfCorr2 : forall lab t e1 e2,
  (phi_psi_entail_corr Phi Psi (.corr lab)) ->
  has_type Phi Psi Delta Gamma e1 t ->
  has_type Phi Psi Delta Gamma (.if_c lab e1 e2) t
| T_Sub : forall e t t',
  subtype Phi Psi Delta t t' ->
  has_type Phi Psi Delta Gamma e t ->
  has_type Phi Psi Delta Gamma e t'
| T_CorrCase : forall lab e t,
  has_type Phi ((.corr lab) :: Psi) Delta Gamma e t ->
  has_type Phi ((.not_corr lab) :: Psi) Delta Gamma e t ->
  has_type Phi Psi Delta Gamma (.corr_case lab e) t
| T_CorrCase2 : forall lab e t,
  has_type Phi ((.corr lab) :: Psi) Delta Gamma e t ->
  has_type Phi ((.not_corr lab) :: Psi) Delta Gamma e t ->
  has_type Phi Psi Delta Gamma e t
| T_Annot : forall e t,
  has_type Phi Psi Delta Gamma e t ->
  has_type Phi Psi Delta Gamma (.annot e t) t

-- NEED TO ADD IF STATEMENTS BACK (RELFLECTING NEW CORR DEFS)

theorem simple_var_typing :
  forall x Phi Psi Delta (Gamma : gamma_context l d m),
     has_type Phi Psi Delta Gamma (.var_tm x) (Gamma x) := by
  intro x Phi Psi Delta Gamma
  exact has_type.T_Var x

theorem concrete_typing : @has_type 0 0 0  empty_phi (empty_psi 0) empty_delta empty_gamma .skip .Unit :=
  has_type.T_IUnit
