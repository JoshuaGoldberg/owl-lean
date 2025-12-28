import OwlLean.OwlLang.Owl

namespace Owl

def cond_sym.pretty (c : cond_sym) : String :=
  match c with
  | .leq   => "≤"
  | .geq   => "≥"
  | .gt    => ">"
  | .lt    => "<"
  | .nleq  => "≰"
  | .ngeq  => "≱"
  | .ngt   => "≯"
  | .nlt   => "≮"

instance : ToString cond_sym where
  toString := cond_sym.pretty

def label.pretty (l : label n) : String :=
  match l with
  | .var_label i => "L" ++ toString i.toNat
  | .latl _ => "<lconst>"
  | .ljoin l1 l2 => "(" ++ l1.pretty ++ " ⊔ " ++ l2.pretty ++ ")"
  | .lmeet l1 l2 => "(" ++ l1.pretty ++ " ⊓ " ++ l2.pretty ++ ")"
  | .default => "Ldefault"

instance : ToString (label n) where
  toString := label.pretty


def binary.pretty (b : binary) : String :=
  match b with
  | .bend => "ε"
  | .bzero b' => "0" ++ b'.pretty
  | .bone b' => "1" ++ b'.pretty

instance : ToString binary where
  toString := binary.pretty


def ty.pretty (t : ty l d) : String :=
  match t with
  | .var_ty i => "X" ++ toString i.toNat
  | .Any => "Any"
  | .Unit => "Unit"
  | .Data l => "Data[" ++ l.pretty ++ "]"
  | .Ref t' => "Ref(" ++ t'.pretty ++ ")"
  | .arr t1 t2 => "(" ++ t1.pretty ++ " -> " ++ t2.pretty ++ ")"
  | .prod t1 t2 => "(" ++ t1.pretty ++ " * " ++ t2.pretty ++ ")"
  | .sum t1 t2 => "(" ++ t1.pretty ++ " + " ++ t2.pretty ++ ")"
  | .all t0 t => "forall (" ++ t0.pretty ++ "), " ++ t.pretty
  | .ex t0 t => "exists (" ++ t0.pretty ++ "), " ++ t.pretty
  | .all_l cs l t =>
      "forall(" ++ cs.pretty ++ " " ++ l.pretty ++ "). " ++ t.pretty
  | .t_if l t1 t2 =>
      "if[" ++ l.pretty ++ "] { " ++ t1.pretty ++ " } else { " ++ t2.pretty ++ " }"
  | .Public => "Public"
  | .Sing b => "Sing(" ++ b.pretty ++ ")"
  | .default => "default"

instance : ToString (ty l d) where
  toString := ty.pretty
