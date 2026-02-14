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
  | .var_label n _ => n
  | .latl _ => "<lconst>"
  | .ljoin l1 l2 => "(" ++ l1.pretty ++ " ⊔ " ++ l2.pretty ++ ")"
  | .lmeet l1 l2 => "(" ++ l1.pretty ++ " ⊓ " ++ l2.pretty ++ ")"
  | .default => "Ldefault"

instance : ToString (label n) where
  toString := label.pretty


def rexp.pretty (re : rexp r n) : String :=
  match re with
  | .var i => "r" ++ toString i.toNat
  | .op s r1 r2 => s ++ "(" ++ r1.pretty ++ "," ++ r2.pretty ++ ")"
  | .const b => b
  | .fvar n => "<guid " ++ Lean.Name.toString n ++ ">"
  | .tmvar j => "val(" ++ toString j.toNat ++ ")"

def prop.pretty (p : prop r n) : String :=
  match p with
  | .peq r1 r2 => r1.pretty ++ " = " ++ r2.pretty
  | .pand p1 p2 => p1.pretty ++ " ∧ " ++ p2.pretty
  | .por p1 p2 => p1.pretty ++ " ∨ " ++ p2.pretty
  | .pimpl p1 p2 => p1.pretty ++ " → " ++ p2.pretty
  | .pnot p1 => "¬ " ++ p1.pretty
  | .pall p1 => "∀ ." ++ p1.pretty

def ty.pretty (t : ty l r d n ) : String :=
  match t with
  | .var_ty i => "X" ++ toString i.toNat
  | .Any => "Any"
  | .Unit => "Unit"
  | .refined t p => t.pretty ++ "{" ++ p.pretty ++ "}"
  | .RData l re => "RData[" ++ l.pretty ++ "," ++ re.pretty ++ "]"
  | .Data l => "Data[" ++ l.pretty ++ "]"
  | .Ref t' => "Ref(" ++ t'.pretty ++ ")"
  | .arr t1 t2 => "(" ++ t1.pretty ++ " -> " ++ t2.pretty ++ ")"
  | .union t1 t2 =>  t1.pretty ++ " ∪ " ++ t2.pretty
  | .inter t1 t2 =>  t1.pretty ++ " ∩ " ++ t2.pretty
  | .prod t1 t2 => "(" ++ t1.pretty ++ " * " ++ t2.pretty ++ ")"
  | .sum t1 t2 => "(" ++ t1.pretty ++ " + " ++ t2.pretty ++ ")"
  | .all t0 t => "forall (" ++ t0.pretty ++ "), " ++ t.pretty
  | .ex t0 t => "exists (" ++ t0.pretty ++ "), " ++ t.pretty
  | .ex_r t0 => "exists_r" ++ t0.pretty
  | .all_r t0 => "exists_r" ++ t0.pretty
  | .all_l cs l t =>
      "forall(" ++ cs.pretty ++ " " ++ l.pretty ++ "). " ++ t.pretty
  | .t_if l t1 t2 =>
      "if[" ++ l.pretty ++ "] { " ++ t1.pretty ++ " } else { " ++ t2.pretty ++ " }"
  | .Public => "Public"
  | .default => "default"

instance : ToString (ty l r d n) where
  toString := ty.pretty
