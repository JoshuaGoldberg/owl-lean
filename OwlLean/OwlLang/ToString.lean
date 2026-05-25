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

def LabelTm.pretty (l : LabelTm) : String :=
  match l with
  | .atom x => x
  | .and l1 l2 => "(" ++ l1.pretty ++ " ∧ " ++ l2.pretty ++ ")"
  | .or l1 l2 => "(" ++ l1.pretty ++ " ∨ " ++ l2.pretty ++ ")"
  | .bot => "⊥"

def label.pretty (l : label n) : String :=
  match l with
  | .var_label n _ => n
  | .latl l => l.pretty
  | .ljoin l1 l2 => "(" ++ l1.pretty ++ " ⊔ " ++ l2.pretty ++ ")"
  | .lmeet l1 l2 => "(" ++ l1.pretty ++ " ⊓ " ++ l2.pretty ++ ")"

instance : ToString (label n) where
  toString := label.pretty

mutual
def rexp.pretty (re : rexp s) : String :=
  match re with
  | .fvar nm => nm.toString
  | .var i => "r" ++ toString i.toNat
  | .op s rs => s ++ "(" ++ rs.pretty ++ ")"
  | .const b => b.toString

def rexp_list.pretty (rs : rexp_list s) : String :=
  match rs with
  | .nil => ""
  | .cons r rs => r.pretty ++ "," ++ rs.pretty
end

def prop.pretty (p : prop s) : String :=
  match p with
  | .peq r1 r2 => r1.pretty ++ " = " ++ r2.pretty
  | .pand p1 p2 => p1.pretty ++ " ∧ " ++ p2.pretty
  | .por p1 p2 => p1.pretty ++ " ∨ " ++ p2.pretty
  | .pimpl p1 p2 => p1.pretty ++ " → " ++ p2.pretty
  | .pnot p1 => "¬ " ++ p1.pretty
  | .pall p1 => "∀ ." ++ p1.pretty
  | .ptrue => "True"

instance : ToString (prop s) where
  toString := prop.pretty

mutual
def ty.pretty (t : ty s) : String :=
  match t with
  | .var_ty s i => if s = "_" then "X" ++ toString i.toNat else s
  | .Any => "Any"
  | .Unit => "Unit"
  | .refined t p => t.pretty ++ "{" ++ p.pretty ++ "}"
  | .RData l re => "RData " ++ l.pretty ++ " [" ++ re.pretty ++ "]"
  | .Data l => "Data[" ++ l.pretty ++ "]"
  | .Ref t' => "Ref(" ++ t'.pretty ++ ")"
  | .arr t1 t2 => "(" ++ t1.pretty ++ " -> " ++ t2.pretty ++ ")"
  | .union t1 t2 =>  t1.pretty ++ " ∪ " ++ t2.pretty
  | .inter t1 t2 =>  t1.pretty ++ " ∩ " ++ t2.pretty
  | .prod t1 t2 => "(" ++ t1.pretty ++ " * " ++ t2.pretty ++ ")"
  | .sum t1 t2 => "(" ++ t1.pretty ++ " + " ++ t2.pretty ++ ")"
  | .all t0 t => "forall (" ++ t0.pretty ++ "), " ++ t.pretty
  | .ex t0 t => "exists (" ++ t0.pretty ++ "), " ++ t.pretty
  | .ex_r t0 => "∃ " ++ t0.pretty
  | .all_r t0 => "exists_r" ++ t0.pretty
  | .all_l cs l t =>
      "forall(" ++ cs.pretty ++ " " ++ l.pretty ++ "). " ++ t.pretty
  | .t_if l t1 t2 =>
      "if corr(" ++ l.pretty ++ ") then " ++ t1.pretty ++ " else " ++ t2.pretty ++ " }"
  | .Public => "Public"
  | .admit => "admit"
  | .record s0 => "{" ++ s0.pretty ++ "}"

def ty_record.pretty (r : ty_record s) : String :=
  match r with
  | .nil => ""
  | .cons s t r =>
    match r with
    | .nil => s ++ ": " ++ t.pretty
    | .cons _ _ _ => s ++ ": " ++ t.pretty ++ ", " ++ r.pretty
end

instance : ToString (ty s) where
  toString := ty.pretty


def corruption.pretty (c : corruption s) : String :=
  match c with
  | .corr l => "corr(" ++ l.pretty ++ ")"
  | .not_corr l => "not_corr(" ++ l.pretty ++ ")"

instance : ToString (corruption s) where
  toString := corruption.pretty
