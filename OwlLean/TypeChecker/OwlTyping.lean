import OwlLean.OwlLang.Owl
import OwlLean.OwlLang.ScopeMap
import Lean

open Owl
open Vec

#check vec.cons
def vec.castCons (v : a) (xs : vec a n) (h : n + 1 = m) : vec a m :=
   (xs.cons v).castLength h

abbrev tm_ctx (s : ScopeMap 4) := vec (String × ty (s.restrict 3)) (s.get #Tm)
abbrev ty_var_ctx (s : ScopeMap 3) := vec (String × ty s) (s.get #Ty)
inductive lbl_type where
  | MetaLbl
  | QuantLbl
  deriving Lean.ToExpr, BEq, Repr, DecidableEq
abbrev lbl_ctx (s : ScopeMap 1) := vec (String × cond_sym × label s × lbl_type) (s.get #L)

def tm_ctx.bumpTy  (ctx : tm_ctx s) : tm_ctx (s.bump #Ty) :=
  let ctx' := ctx.map fun _ (n, t) => (n, t.rename ((s.lift #Ty).restrict (by simp)))
  ctx'.castLength (by simp)

@[simp]
abbrev corr_ctx s := (List (corruption s))

def tm_ctx.cast (ctx : tm_ctx s) (h : s = s' := by simp) : tm_ctx s' :=
  h ▸ ctx

def ty_var_ctx.cast (ctx : ty_var_ctx s) (h : s = s' := by simp) : ty_var_ctx s' :=
  h ▸ ctx

def lbl_ctx.cast (ctx : lbl_ctx s) (h : s = s' := by simp) : lbl_ctx s' :=
  h ▸ ctx

def corr_ctx.cast (ctx : corr_ctx s) (h : s = s' := by simp) : corr_ctx s' :=
  h ▸ ctx

-- The rest here ...

/-

@[simp]
def gamma_context (l : Nat) r (d : Nat) (m : Nat)  := Fin m -> ty l r d 0
@[simp]
def delta_context (l : Nat) r (d : Nat)  := Fin d -> ty l r d 0
@[simp]
def phi_context (l : Nat) := Fin l -> (cond_sym × label l)

abbrev gamma_context_repr (l r d m  : Nat) := vec (ty l r d 0) m

instance : Lean.ToExpr (gamma_context_repr l r d m ) := by
  infer_instance

abbrev delta_context_repr l r d := vec (ty l r d 0) d

instance : Lean.ToExpr (delta_context_repr l r d) := by
  infer_instance

abbrev phi_context_repr l := vec (cond_sym × label l) l

deriving instance Repr for cond_sym
deriving instance Repr for label
deriving instance Repr for vec
deriving instance Repr for phi_context_repr

instance : Lean.ToExpr (phi_context_repr l) := by
  infer_instance

@[simp]
def empty_gamma : gamma_context l r d 0  :=
  fun (i : Fin 0) => nomatch i

@[simp]
def empty_delta : delta_context l r 0 :=
  fun (i : Fin 0) => nomatch i

@[simp]
def empty_phi : (phi_context 0) :=
  fun (i : Fin 0) => nomatch i

@[simp]
def lift_delta (Delta : Fin (d + 1) -> ty l r d 0 )
  : delta_context l r (d + 1)
  := fun i => ren_ty id id shift id (Delta i)

@[simp]
def lift_delta_l (Delta : delta_context l r d )
  : delta_context (l + 1) r d
  := fun i => ren_ty shift id id id (Delta i)

@[simp]
def lift_delta_r (Delta : delta_context l r d)
  : delta_context l (r + 1) d
  := fun i => ren_ty id shift id id (Delta i)

@[simp]
def lift_gamma_d (Gamma : gamma_context l r d m )
  : gamma_context l r (d + 1) m
  := fun i => ren_ty id id shift id (Gamma i)

@[simp]
def lift_gamma_l (Gamma : gamma_context l r d m )
  : gamma_context (l + 1) r d m
  := fun i => ren_ty shift id id id (Gamma i)

@[simp]
def lift_gamma_r (Gamma : gamma_context l r d m )
  : gamma_context l (r + 1) d m
  := fun i => ren_ty id shift id id (Gamma i)

-/


@[simp]
abbrev Owl.label.interp (l : label (ScopeMap.empty _)) : LabelTm :=
  match l with
  | .ljoin l1 l2 => LabelTm.and l1.interp l2.interp
  | .latl l => l
  | .var_label _ i => nomatch i
  | .lmeet l1 l2 => LabelTm.or l1.interp l2.interp


@[simp]
def negate_cond (co : constr s) : constr s :=
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
def valid_constraint (co : constr (ScopeMap.empty _)) : Prop :=
  match co with
  | (.condition .leq x y) => LabelTm.leq (x.interp) (y.interp)
  | (.condition .geq x y) => LabelTm.leq (y.interp) (x.interp)
  | (.condition .gt x y) => LabelTm.leq (y.interp) (x.interp) /\ ¬ LabelTm.leq (x.interp) (y.interp)
  | (.condition .lt x y) => LabelTm.leq (x.interp) (y.interp) /\ ¬ LabelTm.leq (y.interp) (x.interp)
  | (.condition .nleq x y) => ¬ LabelTm.leq (y.interp) (x.interp)
  | (.condition .ngeq x y) => ¬ LabelTm.leq (y.interp) (x.interp)
  | (.condition .ngt x y) => ¬ LabelTm.leq (y.interp) (x.interp) \/ LabelTm.leq (x.interp) (y.interp)
  | (.condition .nlt x y) => ¬ LabelTm.leq (x.interp) (y.interp) \/ ¬ LabelTm.leq (y.interp) (x.interp)


@[simp]
abbrev lbl_interp s := LabelSubst s (ScopeMap.empty _)


abbrev lbl_interp.holds (i : lbl_interp s) (co : constr s) : Prop :=
 match co with
 | .condition c l1 l2 => valid_constraint (.condition c (l1.subst i) (l2.subst i))



@[simp]
abbrev lbl_interp.valid (i : lbl_interp s) (c : lbl_ctx s) :=
  c.All fun v (_, (s, l, _)) => i.holds (.condition s (label.var_label "_" v) l)

@[simp]
abbrev lbl_ctx.entails (c : lbl_ctx s) (co : constr s) : Prop :=
  (forall (interp : lbl_interp s),
    interp.valid c ->
    interp.holds co
  )

structure CorruptionSet where
  is_corrupt : LabelTm -> Prop
  has_bot : is_corrupt LabelTm.bot
  downward_closed : forall l l',
                    is_corrupt l' ->
                    LabelTm.leq l l' ->
                    is_corrupt l
  join_corrupt : forall l1 l2,
                    is_corrupt l1 ->
                    is_corrupt l2 ->
                    is_corrupt (LabelTm.and l1 l2)


@[grind .]
theorem CorruptionSet.by_downwards_closed (C : CorruptionSet) :
  C.is_corrupt l ->
  LabelTm.leq l' l ->
  C.is_corrupt l' := by
    intros h1 h2
    apply C.downward_closed
    apply h1
    assumption

@[grind .]
theorem CorruptionSet.has_bot_pf (C : CorruptionSet) :
  C.is_corrupt LabelTm.bot := by {
      apply C.has_bot
  }

@[grind .]
theorem CorruptionSet.is_corrupt_join (C : CorruptionSet) :
  C.is_corrupt l1 ->
  C.is_corrupt l2 ->
  C.is_corrupt (LabelTm.and l1 l2) := by
    apply C.join_corrupt

abbrev corr_ctx.bumpLbl (c : corr_ctx s) :=
  c.map fun corr => corr.rename (s.lift #L)

abbrev corr_ctx.subst (c : corr_ctx s) (i : lbl_interp s) : corr_ctx (ScopeMap.empty _) :=
  c.map fun corr => corr.subst i

@[simp]
abbrev CorruptionSet.satifies (C : CorruptionSet) (psi : corr_ctx (ScopeMap.empty _)) : Prop :=
  List.foldr (fun i acc =>
    acc ∧ match i with
    | corruption.corr x => C.is_corrupt x.interp
    | .not_corr x => ¬ (C.is_corrupt x.interp)
  ) True psi

@[simp]
def lbl_ctx.inconsistent_with (lc : lbl_ctx s) (psi : corr_ctx s) : Prop :=
  forall (pm : lbl_interp s) (C : CorruptionSet),
    pm.valid lc ->
    C.satifies (psi.subst pm) ->
    False


@[simp]
def  entail_corr (phictx : lbl_ctx s) (psictx : corr_ctx s) (co : corruption s) : Prop :=
  (forall (pm : lbl_interp s) (C : CorruptionSet),
    (pm.valid phictx) ->
    C.satifies (psictx.subst pm) ->
    C.satifies (corr_ctx.subst [co] pm))
