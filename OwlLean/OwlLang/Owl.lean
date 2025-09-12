namespace Owl

structure Lattice where
  labels : Type
  leq    : labels -> labels -> Bool
  bot    : labels
  join   : labels -> labels -> labels
  meet   : labels -> labels -> labels

axiom L : Lattice

abbrev Lcarrier : Type := L.labels

inductive binary : Type
| bzero : binary -> binary
| bone : binary -> binary
| bend : binary
deriving Repr

inductive cond_sym : Type
| leq : cond_sym
| geq : cond_sym
| gt : cond_sym
| lt : cond_sym
| nleq : cond_sym
| ngeq : cond_sym
| ngt : cond_sym
| nlt : cond_sym
deriving Repr

instance : Repr Owl.Lcarrier where
  reprPrec _ _ := "<Lattice Label>"

inductive label : Nat -> Type where
| var_label : Fin n -> label n
| latl : Lcarrier -> label n
| ljoin : label n -> label n -> label n
| lmeet : label n -> label n -> label n
deriving Repr

inductive constr (n_label : Nat) : Type where
| condition : cond_sym -> label n_label -> label n_label -> constr n_label
deriving Repr

inductive ty : Nat -> Nat-> Type where
| var_ty : Fin n_ty -> ty n_label n_ty
| Any : ty n_label n_ty
| Unit : ty n_label n_ty
| Data : label n_label -> ty n_label n_ty
| Ref : ty n_label n_ty -> ty n_label n_ty
| arr : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
| prod : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
| sum : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
| all : ty n_label n_ty -> ty n_label (n_ty + 1) -> ty n_label n_ty
| ex : ty n_label n_ty -> ty n_label (n_ty + 1) -> ty n_label n_ty
| all_l : cond_sym -> label n_label -> ty (n_label + 1) n_ty -> ty n_label n_ty
| t_if : constr n_label -> ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
deriving Repr

inductive Dist (a : Type) : Type where
| ret  : a -> Dist a
| flip : (Bool -> Dist a) → Dist a

abbrev op := binary -> binary -> Dist binary

instance : Repr Owl.op where
  reprPrec _ _ := "<Operation>"

inductive tm : Nat -> Nat -> Nat -> Type where
| var_tm : Fin n_tm -> tm n_label n_ty n_tm
| error : tm n_label n_ty n_tm
| skip : tm n_label n_ty n_tm
| bitstring : binary -> tm n_label n_ty n_tm
| loc : Nat -> tm n_label n_ty n_tm
| fixlam : tm n_label n_ty ((n_tm + 1) + 1) -> tm n_label n_ty n_tm
| tlam : tm n_label (n_ty + 1) n_tm -> tm n_label n_ty n_tm
| l_lam : tm (n_label + 1) n_ty n_tm -> tm n_label n_ty n_tm
| Op : op -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| zero : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| app : tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| alloc : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| dealloc : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| assign : tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| tm_pair : tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| left_tm : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| right_tm : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| inl : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| inr : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| case :
    tm n_label n_ty n_tm ->
    tm n_label n_ty (n_tm + 1) -> tm n_label n_ty (n_tm + 1) -> tm n_label n_ty n_tm
| tapp : tm n_label n_ty n_tm -> ty n_label n_ty -> tm n_label n_ty n_tm
| lapp : tm n_label n_ty n_tm -> label n_label -> tm n_label n_ty n_tm
| pack : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| unpack : tm n_label n_ty n_tm -> tm n_label (n_ty + 1) (n_tm + 1) -> tm n_label n_ty n_tm
| if_tm :
    tm n_label n_ty n_tm ->
    tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| if_c :
    constr n_label -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm -> tm n_label n_ty n_tm
| sync : tm n_label n_ty n_tm -> tm n_label n_ty n_tm
deriving Repr

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

def ren (m n : Nat) : Type := Fin m → Fin n

def shift : ren n (n + 1) :=
  fun x => Fin.succ x

def var_zero : Fin (n + 1) :=
  0

def funcomp (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x)

def cons (x : X) (f : Fin n -> X) (m : Fin (n + 1)) : X :=
  match m with
  | ⟨0,_⟩ => x
  | ⟨k+1, hk⟩ =>
      have hk' : k < n := Nat.lt_of_succ_lt_succ hk
      let i : Fin n := ⟨k, hk'⟩
      (f i)

def up_ren (xi : ren m n) : ren (m + 1) (n + 1) :=
  cons var_zero (funcomp shift xi)

def upRen_ty_label (xi : Fin m → Fin n) : Fin m → Fin n :=
  xi

def upRen_ty_ty (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  up_ren xi

def upRen_label_label (xi : Fin m -> Fin n) : Fin (m + 1) -> Fin (n + 1) :=
  up_ren xi

def upRen_label_ty (xi : Fin m -> Fin n) : Fin m -> Fin n :=
  xi

def ren_label
  (xi_label : Fin m_label → Fin n_label)
  (s : label m_label) : label n_label :=
  match s with
  | .var_label s0 => label.var_label (xi_label s0)
  | .latl s0 => label.latl s0
  | .ljoin s0 s1 => label.ljoin (ren_label xi_label s0) (ren_label xi_label s1)
  | .lmeet s0 s1 => label.lmeet (ren_label xi_label s0) (ren_label xi_label s1)

def ren_constr
  (xi_label : Fin m_label -> Fin n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | .condition s0 s1 s2 => .condition s0 (ren_label xi_label s1) (ren_label xi_label s2)

def ren_ty
(xi_label : Fin m_label -> Fin n_label) (xi_ty : Fin m_ty -> Fin n_ty)
(s : ty m_label m_ty) : ty n_label n_ty :=
  match s with
  | .var_ty s0 => .var_ty (xi_ty s0)
  | .Any => .Any
  | .Unit => .Unit
  | .Data s0 => .Data (ren_label xi_label s0)
  | .Ref s0 => .Ref (ren_ty xi_label xi_ty s0)
  | .arr s0 s1 =>
      .arr (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | .prod s0 s1 =>
      .prod (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | .sum s0 s1 =>
      .sum (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | .all s0 s1 =>
      .all (ren_ty xi_label xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty) s1)
  | .ex s0 s1 =>
      .ex (ren_ty xi_label xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty) s1)
  | .all_l s0 s1 s2 =>
      .all_l s0 (ren_label xi_label s1)
        (ren_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty) s2)
  | .t_if s0 s1 s2 =>
      .t_if (ren_constr xi_label s0) (ren_ty xi_label xi_ty s1)
        (ren_ty xi_label xi_ty s2)

def subst_label
(sigma_label : Fin m_label -> label n_label) (s : label m_label) :
label n_label :=
  match s with
  | .var_label s0 => sigma_label s0
  | .latl s0 => .latl s0
  | .ljoin s0 s1 =>
      .ljoin (subst_label sigma_label s0) (subst_label sigma_label s1)
  | .lmeet s0 s1 =>
      .lmeet (subst_label sigma_label s0) (subst_label sigma_label s1)

def subst_constr
  (sigma_label : Fin m_label -> label n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | .condition s0 s1 s2 =>
      .condition s0 (subst_label sigma_label s1)
        (subst_label sigma_label s2)

def up_ty_label (sigma : Fin m -> label n_label)
  : Fin m -> label n_label :=
    (funcomp (ren_label id) sigma)

def up_ty_ty
  (sigma : Fin m -> ty n_label n_ty) : Fin (m + 1) -> ty n_label (n_ty + 1) :=
    (cons (.var_ty var_zero)
         (funcomp (ren_ty id shift) sigma))

def up_label_label
  (sigma : Fin m -> label n_label) : Fin (m + 1) -> label (n_label + 1) :=
    (cons (.var_label var_zero)
         (funcomp (ren_label shift) sigma))

def up_label_ty
  (sigma : Fin m -> ty n_label n_ty) : Fin m -> ty (n_label + 1) n_ty :=
    (funcomp (ren_ty shift id) sigma)

def subst_ty
(sigma_label : Fin m_label -> label n_label)
(sigma_ty : Fin m_ty -> ty n_label n_ty) (s : ty m_label m_ty) :
ty n_label n_ty :=
  match s with
  | .var_ty s0 => sigma_ty s0
  | .Any => .Any
  | .Unit => .Unit
  | .Data s0 => .Data (subst_label sigma_label s0)
  | .Ref s0 => .Ref (subst_ty sigma_label sigma_ty s0)
  | .arr s0 s1 =>
      .arr (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | .prod s0 s1 =>
      .prod (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | .sum s0 s1 =>
      .sum (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | .all s0 s1 =>
      .all (subst_ty sigma_label sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty) s1)
  | .ex s0 s1 =>
      .ex (subst_ty sigma_label sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty) s1)
  | .all_l s0 s1 s2 =>
      .all_l s0 (subst_label sigma_label s1)
        (subst_ty (up_label_label sigma_label) (up_label_ty sigma_ty) s2)
  | .t_if s0 s1 s2 =>
      .t_if (subst_constr sigma_label s0)
        (subst_ty sigma_label sigma_ty s1) (subst_ty sigma_label sigma_ty s2)

end Owl
