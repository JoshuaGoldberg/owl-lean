import Lean
import OwlLean.OwlLang.Owl

open Owl

/-- Names of label parameters (P), refinement variables (R), type variables (D), term variables (G). -/
abbrev TCtx := List String

@[simp]
def TCtx.lookup (t : TCtx) (s : String) : Option (Fin t.length) :=
  match t with
  | [] => .none
  | x::xs =>
    if x == s then .some ⟨0, by simp [List.length]⟩ else
      match TCtx.lookup xs s with
      | .none => .none
      | .some i => .some ⟨1 + i, by
        simp [List.length]
        omega⟩

/-- Interpret a list as a map `Fin xs.length → α` (head is index 0). -/
@[simp]
def list_to_finmap : (xs : List t) → Fin xs.length → t
  | [] => Fin.elim0
  | x :: xs => cons x (list_to_finmap xs)

def Fin.from_zero {α : Sort _} (i : Fin 0) : α := nomatch i
