import OwlLean.OwlLang.Owl
import Lean

open Owl


/--
Type for an n-length array of type `α` as an inductive type.
-/
inductive vec (α : Type u) : Nat → Type u
| nil  : vec α 0
| cons : α → vec α n → vec α (n + 1)
  deriving Lean.ToExpr

def vec.map (xs : vec a n) (f : a -> b) : vec b n :=
  match xs with
  | nil => nil
  | cons x ys => cons (f x) (ys.map f)

def vec.get (v : vec a n) (i : Fin n) : a :=
  match v with
  | nil => nomatch i
  | cons x xs => if h : i = 0 then x else xs.get (Fin.pred i h)

def vec.toList (v : vec a n) : List a :=
  match v with
  | nil => []
  | cons x xs => x :: xs.toList

abbrev tm_ctx (s : Scope) := vec (ty s) s.nTm
abbrev ty_var_ctx (s : Scope) := vec (ty s) s.nTy
abbrev lbl_ctx (s : Scope) := vec (cond_sym × label s) s.nLbl

def tm_ctx.bumpTy {s : Scope} (ctx : tm_ctx s) : tm_ctx s.bumpTy :=
  ctx.map fun t => t.rename Scope.liftTy

@[simp]
def vec.All (v : vec a n) (p : Fin n -> a -> Prop) : Prop :=
  match v with
  | nil => True
  | cons x xs => p 0 x /\ xs.All (fun i x => p (Fin.succ i) x)

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

-- Convert from labels down to lattice elements
@[simp]
def interp_lattice (l : label Scope.empty) : L.labels :=
  match l with
  | .latl x => x
  | .ljoin x y => (L.join (interp_lattice x) (interp_lattice y))
  | .lmeet x y => (L.meet (interp_lattice x) (interp_lattice y))
  | .var_label _fail n => nomatch n
  | .default => L.bot

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
def valid_constraint (co : constr Scope.empty) : Prop :=
  match co with
  | (.condition .leq x y) => L.leq (interp_lattice x) (interp_lattice y) = true
  | (.condition .geq x y) => L.leq (interp_lattice y) (interp_lattice x) = true
  | (.condition .gt x y) => L.leq (interp_lattice y) (interp_lattice x) = true /\ L.leq (interp_lattice x) (interp_lattice y) = false
  | (.condition .lt x y) => L.leq (interp_lattice x) (interp_lattice y) = true /\ L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .nleq x y) => L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .ngeq x y) => L.leq (interp_lattice y) (interp_lattice x) = false
  | (.condition .ngt x y) => L.leq (interp_lattice y) (interp_lattice x) = false \/ L.leq (interp_lattice x) (interp_lattice y) = true
  | (.condition .nlt x y) => L.leq (interp_lattice x) (interp_lattice y) = false \/ L.leq (interp_lattice y) (interp_lattice x) = false


abbrev lbl_interp s := Scope.subst s Scope.empty


abbrev lbl_interp.holds (i : lbl_interp s) (co : constr s) : Prop :=
 match co with
 | .condition c l1 l2 => valid_constraint (.condition c (l1.subst i) (l2.subst i))



abbrev lbl_interp.valid (i : lbl_interp s) (c : lbl_ctx s) :=
  c.All fun v (s, l) => i.holds (.condition s (label.var_label "_" v) l)

abbrev lbl_ctx.entails (c : lbl_ctx s) (co : constr s) : Prop :=
  (forall (interp : lbl_interp s),
    interp.valid c ->
    interp.holds co
  )

structure CorruptionSet where
  is_corrupt : label Scope.empty -> Prop
  has_bot : is_corrupt (label.latl L.bot)
  downward_closed : forall l l',
                    is_corrupt l' ->
                    L.leq (interp_lattice l) (interp_lattice l') = true ->
                    is_corrupt l
  join_corrupt : forall l1 l2,
                    is_corrupt l1 ->
                    is_corrupt l2 ->
                    is_corrupt (l1.ljoin l2)


@[grind .]
theorem CorruptionSet.by_downwards_closed (C : CorruptionSet) :
  C.is_corrupt l ->
  Owl.L.leq (interp_lattice l') (interp_lattice l) = true ->
  C.is_corrupt l' := by
    intros h1 h2
    apply C.downward_closed
    apply h1
    assumption

@[simp, grind .]
theorem CorruptionSet.has_bot_pf (C : CorruptionSet) :
  C.is_corrupt (label.latl Owl.LabelTm.bot) := by {
      apply C.has_bot
  }

@[grind .]
theorem CorruptionSet.is_corrupt_bot (C : CorruptionSet) :
  C.is_corrupt (label.latl Owl.LabelTm.bot) := by
    apply C.has_bot

@[grind .]
theorem CorruptionSet.is_corrupt_join (C : CorruptionSet) :
  C.is_corrupt l1 ->
  C.is_corrupt l2 ->
  C.is_corrupt (l1.ljoin l2) := by
    apply C.join_corrupt

@[simp]
theorem CorruptionSet.is_corrupt_join_bot (C : CorruptionSet) :
  C.is_corrupt ((label.latl Owl.LabelTm.bot).ljoin
                (label.latl Owl.LabelTm.bot)) := by
    grind





@[simp]
abbrev corr_ctx s := (List (corruption s))

abbrev corr_ctx.bumpTy (c : corr_ctx s) :=
  c.map fun corr => corr.rename Scope.liftTy

abbrev corr_ctx.bumpRef (c : corr_ctx s) :=
  c.map fun corr => corr.rename Scope.liftRef

abbrev corr_ctx.bumpLbl (c : corr_ctx s) :=
  c.map fun corr => corr.rename Scope.liftLbl

abbrev corr_ctx.subst (c : corr_ctx s) (i : lbl_interp s) : corr_ctx Scope.empty :=
  c.map fun corr => corr.subst i

@[simp]
abbrev CorruptionSet.satifies (C : CorruptionSet) (psi : corr_ctx Scope.empty) : Prop :=
  List.foldr (fun i acc =>
    acc ∧ match i with
    | corruption.corr x => C.is_corrupt x
    | .not_corr x => ¬ (C.is_corrupt x)
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
