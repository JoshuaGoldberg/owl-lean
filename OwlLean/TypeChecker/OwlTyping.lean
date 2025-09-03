import OwlLean.OwlLang.Owl
open Owl

-- sanity checks
#check (tm.error : tm 0 0)
#check (ty.Any : ty 0 0)

def gamma_context (l : Nat) (d : Nat) (m : Nat) :=   Fin m -> ty l d
def delta_context (l : Nat) (d : Nat) := Fin d -> ty l d
def phi_context (l : Nat) := (List (constr l))

def empty_gamma : gamma_context l d 0 :=
  fun (i : Fin 0) => nomatch i

def empty_delta : delta_context l 0 :=
  fun (i : Fin 0) => nomatch i

def empty_phi : (phi_context l) := []

def lift_delta (Delta : Fin (d + 1) -> ty l d)
  : delta_context l (d + 1)
  := fun i => ren_ty id shift (Delta i).
