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

inductive cond_sym : Type
| leq : cond_sym
| geq : cond_sym
| gt : cond_sym
| lt : cond_sym
| nleq : cond_sym
| ngeq : cond_sym
| ngt : cond_sym
| nlt : cond_sym

inductive label : Nat -> Type where
| varLabel : Fin n -> label n
| latl : Lcarrier -> label n
| ljoin : label n -> label n -> label n
| lmeet : label n -> label n -> label n

inductive constr (n_label : Nat) : Type where
| condition : cond_sym -> label n_label -> label n_label -> constr n_label

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

inductive Dist (a : Type) : Type where
| ret  : a -> Dist a
| flip : (Bool -> Dist a) → Dist a

abbrev op := binary -> binary -> Dist binary

inductive tm : Nat -> Nat -> Type where
| var_tm : Fin n_tm -> tm n_label n_tm
| error : tm n_label n_tm
| skip : tm n_label n_tm
| bitstring : binary -> tm n_label n_tm
| loc : nat -> tm n_label n_tm
| fixlam : tm n_label ((n_tm + 1) + 1) -> tm n_label n_tm
| tlam : tm n_label n_tm -> tm n_label n_tm
| l_lam : tm (n_label + 1) n_tm -> tm n_label n_tm
| Op : op -> tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| zero : tm n_label n_tm -> tm n_label n_tm
| app : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| alloc : tm n_label n_tm -> tm n_label n_tm
| dealloc : tm n_label n_tm -> tm n_label n_tm
| assign : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| tm_pair : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| left_tm : tm n_label n_tm -> tm n_label n_tm
| right_tm : tm n_label n_tm -> tm n_label n_tm
| inl : tm n_label n_tm -> tm n_label n_tm
| inr : tm n_label n_tm -> tm n_label n_tm
| case :
    tm n_label n_tm ->
    tm n_label (n_tm + 1) -> tm n_label (n_tm + 1) -> tm n_label n_tm
| tapp : tm n_label n_tm -> tm n_label n_tm
| lapp : tm n_label n_tm -> label n_label -> tm n_label n_tm
| pack : tm n_label n_tm -> tm n_label n_tm
| unpack : tm n_label n_tm -> tm n_label (n_tm + 1) -> tm n_label n_tm
| if_tm :
    tm n_label n_tm ->
    tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| if_c :
    constr n_label -> tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
| sync : tm n_label n_tm -> tm n_label n_tm

-- sanity checks
#check (tm.error : tm 0 0)
#check (ty.Any : ty 0 0)

end Owl
