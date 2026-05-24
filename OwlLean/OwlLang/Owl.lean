import Lean
import OwlLean.OwlLang.ScopeMap

open ScopeMap

namespace Owl


-- structure Lattice where
--   labels : Type
--   leq    : labels -> labels -> Prop
--   bot    : labels
--   bot_proof : forall (l : labels), (leq bot l) = true
--   join   : labels -> labels -> labels
--   meet   : labels -> labels -> labels
--   leq_trans : forall l1 l2 l3, leq l1 l2 -> leq l2 l3 -> leq l1 l3
--   leq_refl : forall l, leq l l
--   bot_all : forall l, leq bot l
--   join_le : forall l1 l2 l3, leq l1 l3 -> leq l2 l3 -> leq (join l1 l2) l3

inductive LabelTm where
  | atom : String -> LabelTm
  | and : LabelTm -> LabelTm -> LabelTm
  | or : LabelTm -> LabelTm -> LabelTm
  | bot : LabelTm
  deriving BEq, Repr, Lean.ToExpr

@[simp]
def LabelTm.interp (t : LabelTm) (p : String -> Bool) : Bool :=
  match t with
  | .atom x => p x
  | .and x y => x.interp p && y.interp p
  | .or x y => x.interp p || y.interp p
  | .bot => true

-- l2 implies l1
def LabelTm.leq (l1 : LabelTm) (l2 : LabelTm) :=
  forall p, (! l2.interp p) || l1.interp p

-- def labelTmLattice : Lattice := {
--     labels := LabelTm,
--     leq := LabelTm.leq,
--     bot := .bot,
--     bot_proof := by
--       intros l
--       simp [LabelTm.leq]
--       simp [LabelTm.interp]
--     join := .and,
--     meet := .or,
--     leq_trans := by
--       intros l1 l2 l3
--       unfold LabelTm.leq
--       intros h1 h2 p
--       grind
--     leq_refl := by
--       unfold LabelTm.leq
--       grind
--     bot_all := by
--       unfold LabelTm.leq
--       simp [LabelTm.interp]
--     join_le := by
--       intros l1 l2 l3 h1 h2
--       simp [LabelTm.leq, LabelTm.interp] at *
--       intros
--       grind
-- }



def lattice_leq_trans : forall {l1 l2 l3}, LabelTm.leq l1 l2 -> LabelTm.leq l2 l3 -> LabelTm.leq l1 l3 :=
  fun {l1 l2 l3} => by
     intros
     grind [LabelTm.leq]


grind_pattern lattice_leq_trans => LabelTm.leq l1 l2, LabelTm.leq l2 l3

def lattice_leq_refl : forall {l}, LabelTm.leq l l := fun {l} => by
  grind [LabelTm.leq]

grind_pattern lattice_leq_refl => LabelTm.leq l l

def lattice_bot_all : forall {l}, LabelTm.leq LabelTm.bot l := fun {l} => by
  simp [LabelTm.leq]

grind_pattern lattice_bot_all => LabelTm.leq LabelTm.bot l

def lattice_join_bot : forall {l}, LabelTm.leq (LabelTm.and LabelTm.bot l) l := by
  intros
  simp [LabelTm.leq]

grind_pattern lattice_join_bot => (LabelTm.and LabelTm.bot l)



structure opaqueSyntax where
  inner : Lean.Syntax

instance : Repr opaqueSyntax where
  reprPrec _ _ := f!"<syntax>"

open Lean

inductive cond_sym : Type
| leq : cond_sym
| geq : cond_sym
| gt : cond_sym
| lt : cond_sym
| nleq : cond_sym
| ngeq : cond_sym
| ngt : cond_sym
| nlt : cond_sym
deriving Repr, DecidableEq, Lean.ToExpr

syntax (name := Lvar) "#L" : term
macro_rules
  | `(term| #L) => `(0)

syntax (name := Rvar) "#R" : term
macro_rules
  | `(term| #R) => `(1)

syntax (name := Tyvar) "#Ty" : term
macro_rules
  | `(term| #Ty) => `(2)

syntax (name := Tmvar) "#Tm" : term
macro_rules
  | `(term| #Tm) => `(3)

inductive label : ScopeMap 1 -> Type where
| var_label : String -> Fin (s.get 0) -> label s
| latl : LabelTm -> label s
| ljoin : label s -> label s -> label s
| lmeet : label s -> label s -> label s
deriving Repr, BEq, Lean.ToExpr


inductive corruption : ScopeMap 1 -> Type where
| corr : label s -> corruption s
| not_corr : label s -> corruption s
deriving Repr, BEq, Lean.ToExpr

inductive constr  : ScopeMap 1 -> Type where
| condition : cond_sym -> label s -> label s -> constr s
deriving Repr, BEq, Lean.ToExpr

abbrev GUId := Nat


deriving instance BEq, Lean.ToExpr for String.Pos.Raw
deriving instance BEq, Lean.ToExpr for Substring.Raw
deriving instance BEq, Lean.ToExpr for Lean.SourceInfo
deriving instance BEq, Lean.ToExpr for Lean.Syntax
deriving instance BEq, Lean.ToExpr for Owl.opaqueSyntax


mutual
inductive rexp : ScopeMap 2 -> Type where
  | fvar : Lean.Name -> rexp s
  | var : Fin (s.get #R) -> rexp s
  | op : String -> rexp_list s -> rexp s
  | const : List Char -> rexp s
deriving Repr, BEq, Lean.ToExpr

inductive rexp_list : ScopeMap 2 -> Type where
  | nil : rexp_list s
  | cons : rexp s -> rexp_list s -> rexp_list s
  deriving Repr, BEq, Lean.ToExpr
end

def rexp_list.mk (rs : List (rexp s)) : rexp_list s :=
  match rs with
  | .nil => .nil
  | .cons r rs => .cons r (rexp_list.mk rs)

def rexp_list.toList (rs : rexp_list s) : List (rexp s) :=
  match rs with
  | .nil => []
  | .cons r rs => r :: rs.toList


inductive prop : ScopeMap 2 -> Type where
  | peq : rexp s -> rexp s -> prop s
  | pand : prop s -> prop s -> prop s
  | por : prop s -> prop s -> prop s
  | pimpl : prop s -> prop s -> prop s
  | pnot : prop s -> prop s
  | pall : prop (s.bump #R) -> prop s
  | ptrue : prop s
  deriving Repr, BEq, Lean.ToExpr



mutual
inductive ty : ScopeMap 3 -> Type where
| var_ty : String -> Fin (s.get #Ty) -> ty s
| Any : ty s
| Unit : ty s
| RData : label (s.restrict 1) -> rexp (s.restrict 2) -> ty s
| Data : label (s.restrict 1) -> ty s
| Ref : ty s -> ty s
| arr : ty s -> ty s -> ty s
| union : ty s -> ty s -> ty s
| inter : ty s -> ty s -> ty s
| prod : ty s -> ty s -> ty s
| sum : ty s -> ty s -> ty s
| all : ty s -> ty (s.bump #Ty) -> ty s
| ex : ty s -> ty (s.bump #Ty) -> ty s
| ex_r : ty (s.bump #R) -> ty s
| all_r : ty (s.bump #R) -> ty s
| all_l : cond_sym -> label (s.restrict 1) -> ty (s.bump #L) -> ty s
| t_if : label (s.restrict 1) -> ty s -> ty s -> ty s
| refined : ty s -> prop (s.restrict 2) -> ty s -- τ ∧ p
-- TODO: p => τ
| Public : ty s
| admit : ty s -- Just for debugging
| record : ty_record s -> ty s
deriving Repr, BEq, Lean.ToExpr

inductive ty_record : ScopeMap 3 -> Type where
| nil : ty_record s
| cons : String -> ty s -> ty_record s -> ty_record s
deriving Repr, BEq, Lean.ToExpr
end


mutual

  inductive tm : ScopeMap 4 -> Type where
   | mk : opaqueSyntax -> tmX s -> tm s
   deriving Repr, Lean.ToExpr

inductive tmX : ScopeMap 4 -> Type where
| admit : tmX s -- Only used for debugging
| var_tm : Fin (s.get #Tm) -> tmX s
| secparam : tmX s
| sample : tm s -> tmX s
| op : String -> tm_list s -> tmX s
| app : tm s -> tm s -> tmX s
| alloc : tm s -> tmX s
| dealloc : tm s -> tmX s
| assign : tm s -> tm s -> tmX s
| tm_pair : tm s -> tm s -> tmX s
| left_tm : tm s -> tmX s
| right_tm : tm s -> tmX s
| inl : tm s -> tmX s
| inr  : tm s -> tmX s
| case :
    tm s ->
    String ->
    tm (s.bump #Tm) ->
    String ->
    tm (s.bump #Tm) -> tmX s

| unit : tmX s
| bitstring : List Char -> tmX s
| loc : Nat -> tmX s
| fixlam : String -> String -> tm ((s.bump #Tm).bump #Tm) -> tmX s
| tlet : String -> tm s -> tm (s.bump #Tm) -> tmX s
| union_elim : String -> tm s -> tm (s.bump #Tm) -> tmX s
| tlam : String -> tm (s.bump #Ty) -> tmX s
| rlam : String -> tm (s.bump #R) -> tmX s
| l_lam : String -> tm (s.bump #L) -> tmX s
| zero : tm s -> tmX s
| tapp : tm s -> ty (s.restrict 3) -> tmX s
| lapp : tm s -> label (s.restrict 1) -> tmX s
| rapp : tm s -> rexp (s.restrict 2) -> tmX s
| pack : ty (s.restrict 3) -> tm s -> tmX s
| rpack : rexp (s.restrict 2) -> tm s -> tmX s
| unpack : tm s -> String -> String -> tm ((s.bump #Ty).bump #Tm) -> tmX s
| get_val : String -> tm s -> tm (s.bump #R) -> tmX s
| if_tm :
    tm s ->
    tm s -> tm s -> tmX s
| if_c :
    label (s.restrict 1) -> tm s -> tm s -> tmX s
| corr_case : label (s.restrict 1) -> tm s -> tmX s
| annot : tm s -> ty (s.restrict 3) -> tmX s
| mk_record : tm_list s -> tmX s
| get_record : String -> tm s -> tmX s
deriving Repr, Lean.ToExpr

inductive tm_list : ScopeMap 4 -> Type where
| nil : tm_list s
| cons : String -> tm s -> tm_list s -> tm_list s
deriving Repr, BEq, Lean.ToExpr

end


def tm_list.toList (t : tm_list s) : List (String × tm s) :=
  match t with
  | .nil => []
  | .cons s e l => (s, e) :: l.toList

def mkTm (t : tmX s) : tm s :=
  tm.mk (.mk Lean.Syntax.missing) t


-- class EqScopeMap (s : ScopeMap N) (t : ScopeMap N) where
--   heq : s = t
--
-- class IsTrue (p : Prop) where
--   pf : p
--
--
--
-- class FinToNat (i : Fin n) (m : outParam Nat) where
--   heq : i.val = m
--
-- instance {x : Fin n}: FinToNat x x.val where
--   heq := rfl
--
-- class LeNat (n : Nat) (m : Nat) where
--   le : n ≤ m
--
-- instance : LeNat 0 0 where
--   le := by simp
--
-- instance [h : LeNat n m] : LeNat n (m + 1) where
--   le := by grind [h.le]
--
-- instance [h : LeNat n m] : LeNat (n + 1) (m + 1) where
--   le := by grind [h.le]
--
-- instance {m1 m2 : ScopeMap 2} {p : prop m1} [h : EqScopeMap m1 m2] : CoeDep (prop m1) p (prop m2) where
--   coe := h.heq ▸ p
--
-- instance [h : IsTrue (n =  m)] {i : Fin n} : CoeDep (Fin n) i (Fin m) where
--   coe := i.cast h.pf
--
-- instance [h : IsTrue (m = n)] {i : Fin n} : CoeDep (Fin n) i (Fin m) where
--   coe := i.cast h.pf.symm
--
-- class SameFin (i : Fin n) (j : Fin m) where
--   same : i.val = j.val
--
-- class NeqFin (i : Fin n) (j : Fin m) where
--   h : ¬ i.val = j.val
--
-- class GeFinNat (i : Fin n) (j : Nat) where
--   h : i.val >= j
--
--
-- instance {s : ScopeMap N} {i : Fin N} {M : Nat} {h h' : M ≤ N} [hiM : GeFinNat i M] : EqScopeMap ((s.bump i).restrict M h) (s.restrict M h') where
--   heq := by
--     simp [ScopeMap.bump_restrict]
--     intros
--     cases hiM
--     grind
--
--
-- instance [h : NeqFin x y] : NeqFin y x where
--   h := by cases h; grind
--
--
--
-- instance [h : SameFin x y] : SameFin y x where
--   same := h.same.symm
--
-- instance : SameFin (1 : Fin 4) (1 : Fin 3) where
--   same := by simp
--
-- instance {s : ScopeMap N} {M : Nat} {hM} {x : Fin M} {y} [hxy : SameFin x y] : IsTrue ((s.restrict M hM).get x = s.get y) where
--   pf := by
--     simp
--     unfold ScopeMap.get
--     congr 1
--     apply Fin.ext
--     simp
--     apply hxy.same
--
-- instance {s : ScopeMap N} {M : Nat} {hM : M <= N} {M' : Nat} {hM' : M' <= M} {h3 : M' <= N} :
--    EqScopeMap ((s.restrict M hM).restrict M' hM') ((s.restrict M' h3))  where
--      heq := by
--       apply ScopeMap.restrict_restrict
--
--
--
--
-- instance {s : ScopeMap N} {x y : Fin N} [h : NeqFin x y] : IsTrue ((s.bump x).get y = s.get y) where
--   pf := by cases h; simp; grind
--
-- instance : NeqFin (1 : Fin 4) (3 : Fin 4) where
--   h := by grind
--
-- instance : NeqFin (0 : Fin 4) (1 : Fin 4) where
--   h := by grind
--
-- instance {s : ScopeMap N} {x : Fin N} : IsTrue ((s.bump x).get x = s.get x + 1) where
--   pf := by simp
--
-- instance {s : ScopeMap N} {x : Fin N} : IsTrue (s.get x + 1 = (s.bump x).get x) where
--   pf := by simp
--
-- instance : SameFin (2 : Fin 3) (2 : Fin 4) where
--   same := by simp
--
-- instance {s : ScopeMap N} (x : Fin N) M h (y : Fin M) [Hsame : SameFin x y] : EqScopeMap ((s.bump x).restrict M h) ((s.restrict M h).bump y) where
--   heq := by
--      simp [ScopeMap.bump_restrict]
--      split
--      congr 1
--      cases Hsame; grind
--      cases y
--      cases x
--      cases Hsame
--      grind
--
--
-- instance : GeFinNat (2 : Fin 4) 1 where
--   h := by simp
--
-- instance [h : EqScopeMap s t] (l : label s) : CoeDep (label s) l (label t) where
--   coe := h.heq ▸ l
--
-- instance [h : EqScopeMap s t] (l : ty s) : CoeDep (ty s) l (ty t) where
--   coe := h.heq ▸ l
--
-- instance [h : EqScopeMap s t] (p : prop s) : CoeDep (prop s) p (prop t) where
--   coe := h.heq ▸ p
--
-- instance {s : ScopeMap N} : EqScopeMap ((s.bump x).bump y) ((s.bump y).bump x) where
--    heq := by simp [ScopeMap.bump_bump]
--
-- instance {s : ScopeMap N} {x : Fin N} {M : Nat} {h : M <= N} {y : Fin M} [heq : SameFin x y] :  EqScopeMap ((s.bump x).restrict M h) ((s.restrict M h).bump y) where
--   heq := by
--     simp [ScopeMap.bump_restrict]
--     split
--     congr 1
--     cases heq
--     grind
--     cases y
--     cases heq
--     grind
--
-- instance {s : ScopeMap N} {x : Fin N} {M : Nat} {h h' : M <= N} [h2 : IsTrue (x >= M)] :  EqScopeMap ((s.bump x).restrict M h) (s.restrict M h') where
--   heq := by
--     simp [ScopeMap.bump_restrict]
--     intros
--     cases h2
--     grind





@[always_inline]
abbrev tm.get (t : tm s) : tmX s :=
  match t with
  | .mk _ v => v

@[simp]
def tm.mkD (t : tmX s) : tm s :=
  let stx := Lean.Syntax.missing
  tm.mk (.mk stx) t

abbrev ren (m n : Nat) : Type := Fin m → Fin n

@[simp]
def shift : ren n (n + 1) :=
  fun x => Fin.succ x

def var_zero : Fin (n + 1) :=
  0

@[simp]
def funcomp (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x)

@[simp]
def cons (x : X) (f : Fin n -> X) (m : Fin (n + 1)) : X :=
  match m with
  | ⟨0,_⟩ => x
  | ⟨k+1, hk⟩ =>
      have hk' : k < n := Nat.lt_of_succ_lt_succ hk
      let i : Fin n := ⟨k, hk'⟩
      (f i)


@[simp]
def upRen_ty_label (xi : Fin m → Fin n) : Fin m → Fin n :=
  xi

@[simp]
def upRen_ty_ty (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  up_ren xi

@[simp]
def upRen_label_label (xi : Fin m -> Fin n) : Fin (m + 1) -> Fin (n + 1) :=
  up_ren xi

@[simp]
def upRen_label_ty (xi : Fin m -> Fin n) : Fin m -> Fin n :=
  xi

@[simp]
def label.rename
  (l : label s) (ren : s.renaming s')
  : label s' :=
  match l with
  | .var_label n s0 => label.var_label n (ren.apply #L s0)
  | .latl s0 => label.latl s0
  | .ljoin s0 s1 => label.ljoin (s0.rename ren) (s1.rename ren)
  | .lmeet s0 s1 => label.lmeet (s0.rename ren) (s1.rename ren)

def constr.rename
  (c : constr s)
  (ren : s.renaming s') :
  constr s' :=
  match c with
  | .condition s0 s1 s2 => .condition s0 (s1.rename ren) (s2.rename ren)

def corruption.rename
  (c : corruption s) (ren : s.renaming s') : corruption s' :=
  match c with
  | .corr l1 => .corr (l1.rename ren)
  | .not_corr l1 => .not_corr (l1.rename ren)


mutual

def rexp.rename (r : rexp s) (ren : s.renaming s') : rexp s' :=
  match r with
  | .fvar nm => .fvar nm
  | .var j => .var (ren.apply #R j)
  | .op n rs => .op n (rs.rename ren)
  | .const b => .const b

  def rexp_list.rename (rs : rexp_list s) (ren : s.renaming s') : rexp_list s' :=
    match rs with
    | .nil => .nil
    | .cons r rs => .cons (r.rename ren) (rs.rename ren)

end

def prop.rename (p : prop s) (ren : s.renaming s') : prop s' :=
  match p with
  | .peq re1 re2 => .peq (re1.rename ren) (re2.rename ren)
  | .pand p1 p2 => .pand (p1.rename ren) (p2.rename ren)
  | .por p1 p2 => .por (p1.rename ren) (p2.rename ren)
  | .pimpl p1 p2 => .pimpl (p1.rename ren) (p2.rename ren)
  | .pnot p1 => .pnot (p1.rename ren)
  | .pall p => .pall (p.rename (ren.bump #R))
  | .ptrue => .ptrue


mutual
@[simp]
def ty.rename (t : ty s) (ren : s.renaming s') : ty s' :=
  match t with
  | .admit => .admit
  | .var_ty s s0 => .var_ty s (ren.apply #Ty s0)
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (s0.rename $ ren.restrict) (re.rename $ ren.restrict)
  | .Data s0 => .Data (s0.rename $ ren.restrict)
  | .Ref s0 => .Ref (s0.rename ren)
  | .arr s0 s1 =>
      .arr (s0.rename ren) (s1.rename ren)
  | .union s0 s1 =>
      .union (s0.rename ren) (s1.rename ren)
  | .inter s0 s1 =>
      .inter (s0.rename ren) (s1.rename ren)
  | .prod s0 s1 =>
      .prod (s0.rename ren) (s1.rename ren)
  | .refined t p =>
      .refined (t.rename ren) (p.rename $ ren.restrict)
  | .sum s0 s1 =>
      .sum (s0.rename ren) (s1.rename ren)
  | .all s0 s1 =>
      .all (s0.rename ren)
           (s1.rename $ ren.bump #Ty)
  | .ex s0 s1 =>
      .ex (s0.rename ren)
           (s1.rename $ ren.bump #Ty)
  | .ex_r t0 => .ex_r (t0.rename $ ren.bump #R)
  | .all_r t0 => .all_r (t0.rename $ ren.bump #R)
  | .all_l s0 s1 s2 =>
      .all_l s0 (s1.rename $ ren.restrict _)
        (s2.rename $ ren.bump #L)
  | .t_if s0 s1 s2 =>
      .t_if (s0.rename $ ren.restrict _) (s1.rename ren)
        (s2.rename ren)
  | .Public => .Public
  | .record s0 => .record (s0.rename ren)

def ty_record.rename (r : ty_record s) (ren : s.renaming s') : ty_record s' :=
  match r with
  | .nil => .nil
  | .cons s s0 s1 => .cons s (s0.rename ren) (s1.rename ren)
end


mutual

def tm.rename
 (t : tm s)
 (ren : s.renaming s')
 : tm s' :=
  match t with
  | .mk stx inner => .mk stx (inner.rename ren)


def tmX.rename (t : tmX s) (ren : s.renaming s') : tmX s' :=
  match t with
  | .admit => .admit
  | .var_tm s0 => .var_tm (ren.apply #Tm s0)
  | .secparam => .secparam
  | .sample s0 => .sample (s0.rename ren)
  | .unit => .unit
  | .get_record s0 s1 => .get_record s0 (s1.rename ren)
  | .bitstring s0 => .bitstring s0
  | .get_val s t0 t1 => .get_val s (t0.rename ren) (t1.rename $ ren.bump #R)
  | .loc s0 => .loc s0
  | .fixlam nm1 nm2 s0 =>
      .fixlam nm1 nm2
        (s0.rename $ (ren.bump #Tm).bump #Tm)
  | .tlam nm s0 =>
      .tlam nm (s0.rename $ ren.bump #Ty)
  | .rlam nm s0 =>
    .rlam
        nm (s0.rename $ ren.bump #R)
  | .tlet nm e1 e2 =>
    .tlet nm (e1.rename ren)
          (e2.rename $ ren.bump #Tm)
  | .union_elim nm e1 e2 =>
    .union_elim nm (e1.rename ren)
                (e2.rename $ ren.bump #Tm)
  | .l_lam nm s0 =>
      .l_lam
        nm (s0.rename $ ren.bump #L)
  | .op n rs =>
      .op n (rs.rename ren)
  | .zero s0 => .zero (s0.rename ren)
  | .app s0 s1 =>
     .app (s0.rename ren)
        (s1.rename ren)
  | .alloc s0 =>
      .alloc (s0.rename ren)
  | .dealloc s0 =>
      .dealloc (s0.rename ren)
  | .assign s0 s1 =>
      .assign (s0.rename ren)
        (s1.rename ren)
  | .tm_pair s0 s1 =>
      .tm_pair (s0.rename ren)
        (s1.rename ren)
  | .left_tm s0 =>
      .left_tm (s0.rename ren)
  | .right_tm s0 =>
      .right_tm (s0.rename ren)
  | .inl s0 => .inl (s0.rename ren)
  | .inr s0 => .inr (s0.rename ren)
  | .case s0 nm1 s1 nm2 s2 =>
      .case (s0.rename ren)
            nm1
            (s1.rename $ ren.bump #Tm)
            nm2
            (s2.rename $ ren.bump #Tm)
  | .tapp s0 s1 =>
      .tapp (s0.rename ren)
        (s1.rename $ ren.restrict)
  | .lapp s0 s1 =>
      .lapp (s0.rename ren)
            (s1.rename $ ren.restrict)
  | .rapp e0 re =>
      .rapp (e0.rename ren)
            (re.rename $ ren.restrict)
  | .pack s s0 => .pack
    (s.rename $ ren.restrict)
    (s0.rename ren)
  | .rpack re t0 => .rpack (re.rename $ ren.restrict) (t0.rename ren)
  | .unpack s0 nm1 nm2 s1 =>
      .unpack (s0.rename ren)
              nm1
              nm2
              (s1.rename $ (ren.bump #Ty).bump #Tm)
  | .if_tm s0 s1 s2 =>
      .if_tm (s0.rename ren)
             (s1.rename ren) (s2.rename ren)
  | .if_c s0 s1 s2 =>
      .if_c (s0.rename $ ren.restrict _)
            (s1.rename ren)
            (s2.rename ren)
  | .corr_case lab e => .corr_case (lab.rename $ ren.restrict _) (e.rename ren)
  | .annot e t => .annot (e.rename ren) (t.rename $ ren.restrict)
  | .mk_record l => .mk_record (l.rename ren)

def tm_list.rename (l : tm_list s) (ren : s.renaming s') : tm_list s' :=
  match l with
  | .nil => .nil
  | .cons s e l => .cons s (e.rename ren) (l.rename ren)
end

abbrev OwlFunctors (x : Fin 3) : ScopeFunctor 3 x :=
  match x with
  | ⟨#L, _⟩ => ⟨fun m => label (m.restrict 1), fun m m' r x => x.rename (r.restrict) , fun i => .var_label "_" (by simpa using i)⟩
  | ⟨#R, _⟩  => ⟨fun m => rexp (m.restrict _), fun m m' r x => x.rename (r.restrict) , fun i => .var (by simpa using i)⟩
  | ⟨#Ty, _⟩ => ⟨fun m => ty m, fun m m' r x => x.rename r, fun i => .var_ty "_" (by simpa using i)⟩
--  | ⟨#Tm, _⟩ => ⟨fun m => Fin (m.get _), fun m m' r i => r.apply _ i, fun i => i⟩


abbrev Subst := ScopeMap.Subst 3 OwlFunctors

abbrev LabelFunctors (x : Fin 1) : ScopeFunctor 1 x :=
  match x with
  | ⟨0, _⟩  => ⟨fun m => label m, fun m m' r x => x.rename r , fun i => .var_label "_" (by simpa using i)⟩

@[simp]
abbrev LabelSubst := ScopeMap.Subst 1 LabelFunctors

abbrev mapM [Monad m] (c : m a) (f : a -> b) : m b :=
  c >>= fun x => pure (f x)

abbrev RexpFunctors (x : Fin 2) : ScopeFunctor 2 x :=
  match x with
  | ⟨#L, _⟩  => ⟨fun m => label (m.restrict 1), fun m m' r x => x.rename (r.restrict) , fun i => .var_label "_" (by simpa using i)⟩
  | ⟨#R, _⟩  => ⟨fun m => rexp m, fun m m' r x => x.rename r, fun i => .var (by simpa using i)⟩
--  | ⟨#Tm, _⟩  => ⟨fun m => Fin (m.get _), fun m m' r i => r.apply _ i, fun i => i⟩

abbrev RexpSubst := ScopeMap.Subst 2 RexpFunctors

def Subst.toLabelSubst (sub : Subst s s') : LabelSubst (s.restrict 1) (s'.restrict 1) :=
  ⟨fun x i =>
    match x with
    | 0 => by
        simp
        exact (sub.apply 0 (by simpa using i))
  ⟩

def Subst.toRexpSubst (sub : Subst s s') : RexpSubst (s.restrict 2) (s'.restrict 2) :=
  ⟨fun x i => by
    unfold RexpFunctors
    match x with
    | #L => simp; exact (sub.apply #L  (by simpa using i))
    | #R => simp; exact (sub.apply #R  (by simpa using i))
--    | #Tm => simp; exact(sub.apply #Tm  (by simpa using i))
    ⟩

abbrev TmFunctors (x : Fin 4) : ScopeFunctor 4 x :=
  match x with
  | ⟨#L, _⟩ => ⟨fun m => label (m.restrict 1), fun m m' r x => x.rename (r.restrict) , fun i => .var_label "_" (by simpa using i)⟩
  | ⟨#R, _⟩  => ⟨fun m => rexp (m.restrict _), fun m m' r x => x.rename (r.restrict) , fun i => .var (by simpa using i)⟩
  | ⟨#Ty, _⟩ => ⟨fun m => ty (m.restrict _), fun m m' r x => x.rename r.restrict, fun i => .var_ty "_" (by simpa using i)⟩
  | ⟨#Tm, _⟩ => ⟨fun m => tmX m, fun m m' r x => x.rename r, fun i => (.var_tm (by simpa using i))⟩

abbrev TmSubst := ScopeMap.Subst 4 TmFunctors

def TmSubst.toSubst (sub : TmSubst s s') : Subst (s.restrict 3) (s'.restrict 3) :=
  ⟨fun x i => by
    match x with
    | #L => simp; exact (sub.apply #L  (by simpa using i))
    | #R => simp; exact (sub.apply #R  (by simpa using i))
    | #Ty => simp; exact (sub.apply #Ty  (by simpa using i))
  ⟩

def TmSubst.toLabelSubst (sub : TmSubst s s') : LabelSubst (s.restrict 1) (s'.restrict 1) :=
  ⟨fun x i => by
    match x with
    | #L => simp; exact (sub.apply #L  (by simpa using i))
  ⟩

def TmSubst.toRexpSubst (sub : TmSubst s s') : RexpSubst (s.restrict 2) (s'.restrict 2) :=
  ⟨fun x i => by
    match x with
    | #L => simp; exact (sub.apply #L  (by simpa using i))
    | #R => simp; exact (sub.apply #R  (by simpa using i))
  ⟩


@[simp]
def label.subst (l : label s) (sub : LabelSubst s s') : label s' :=
  match l with
  | .var_label _ s0 => sub.apply #L s0
  | .latl s0 => .latl s0
  | .ljoin s0 s1 =>
      let s0' := s0.subst sub
      let s1' := s1.subst sub
      .ljoin s0' s1'
  | .lmeet s0 s1 =>
      let s0' := s0.subst sub
      let s1' := s1.subst sub
      .lmeet s0' s1'

@[simp]
def corruption.subst (c : corruption s) (sub : LabelSubst s s') : corruption s' :=
  match c with
  | .corr l1 =>
      let l1' := l1.subst sub
      .corr l1'
  | .not_corr l1 =>
      let l1' := l1.subst sub
      .not_corr l1'

@[simp]
def constr.subst (c : constr s) (sub : LabelSubst s s') : constr s' :=
  match c with
  | .condition s0 s1 s2 =>
      let s1' := s1.subst sub
      let s2' := s2.subst sub
      .condition s0 s1' s2'

mutual
def rexp.subst (r : rexp s) (sub : RexpSubst s s') : rexp s' :=
  match r with
  | .fvar nm => .fvar nm
  | .var j => sub.apply #R j
  | .op n rs => .op n (rs.subst sub)
  | .const b => .const b

def rexp_list.subst (rs : rexp_list s) (sub : RexpSubst s s') : rexp_list s' :=
  match rs with
  | .nil => .nil
  | .cons r rs => .cons (r.subst sub) (rs.subst sub)
end

def prop.subst (p : prop s) (sub : RexpSubst s s') : prop s' :=
  match p with
  | .peq re1 re2 => .peq (re1.subst sub) (re2.subst sub)
  | .pand p1 p2 => .pand (p1.subst sub) (p2.subst sub)
  | .por p1 p2 => .por (p1.subst sub) (p2.subst sub)
  | .pimpl p1 p2 => .pimpl (p1.subst sub) (p2.subst sub)
  | .pnot p1 => .pnot (p1.subst sub)
  | .pall p => .pall (p.subst $ sub.bump #R)
  | .ptrue => .ptrue

mutual
@[simp]
def ty.subst (t : ty s) (sub : Subst s s') : ty s' :=
  match t with
  | .admit => .admit
  | .var_ty _ s0 => sub.apply #Ty s0
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (s0.subst sub.toLabelSubst) (re.subst sub.toRexpSubst)
  | .Data s0 => .Data (s0.subst sub.toLabelSubst)
  | .Ref s0 => .Ref (s0.subst sub)
  | .refined t p => .refined (t.subst sub) (p.subst sub.toRexpSubst)
  | .arr s0 s1 => .arr (s0.subst sub) (s1.subst sub)
  | .union s0 s1 => .union (s0.subst sub) (s1.subst sub)
  | .inter s0 s1 => .inter (s0.subst sub) (s1.subst sub)
  | .prod s0 s1 => .prod (s0.subst sub) (s1.subst sub)
  | .sum s0 s1 => .sum (s0.subst sub) (s1.subst sub)
  | .all s0 s1 =>
      .all (s0.subst sub) (s1.subst $ sub.bump _)
  | .ex s0 s1 =>
      .ex (s0.subst sub) (s1.subst $ sub.bump _)
  | .ex_r t0 =>
      .ex_r (t0.subst $ sub.bump _)
  | .all_r t0 =>
      .all_r (t0.subst $ sub.bump _)
  | .all_l s0 s1 s2 =>
      .all_l s0 (s1.subst sub.toLabelSubst) (s2.subst $ sub.bump _)
  | .t_if s0 s1 s2 =>
      .t_if (s0.subst sub.toLabelSubst) (s1.subst sub) (s2.subst sub)
  | .Public => .Public
  | .record s0 => .record (s0.subst sub)

def ty_record.subst (r : ty_record s) (sub : Subst s s') : ty_record s' :=
  match r with
  | .nil => .nil
  | .cons s s0 s1 => .cons s (s0.subst sub) (s1.subst sub)
end

def _root_.Fin.down (f : Fin (n + 1)) : Option (Fin n) :=
  if h : f < n then .some ⟨f.val, by grind⟩ else none

mutual
 def tm.subst (t : tm s) (sub : TmSubst s s') : tm s' :=
   match t with
   | .mk stx inner => .mk stx (inner.subst sub)

 def tmX.subst (t : tmX s) (sub : TmSubst s s') : tmX s' :=
   match t with
   | .admit => .admit
   | .var_tm s0 => (sub.apply #Tm s0)
   | .secparam => .secparam
   | .sample s0 => .sample (s0.subst sub)
   | .unit => .unit
   | .get_record s0 s1 => .get_record s0 (s1.subst sub)
   | .bitstring s0 => .bitstring s0
   | .get_val s0 s1 s2 => .get_val s0 (s1.subst sub) (s2.subst $ sub.bump #R)
   | .loc s0 => .loc s0
   | .fixlam nm1 nm2 s0 => .fixlam nm1 nm2 (s0.subst $ (sub.bump #Tm).bump #Tm)
   | .tlam nm s0 => .tlam nm (s0.subst $ sub.bump #Ty)
   | .rlam nm s0 => .rlam nm (s0.subst $ sub.bump #R)
   | .tlet nm e1 e2 => .tlet nm (e1.subst sub) (e2.subst $ sub.bump #Tm)
   | .union_elim nm e1 e2 => .union_elim nm (e1.subst sub) (e2.subst $ sub.bump #Tm)
   | .l_lam nm s0 => .l_lam nm (s0.subst $ sub.bump #L)
   | .op n rs => .op n (rs.subst sub)
   | .zero s0 => .zero (s0.subst sub)
   | .app s0 s1 => .app (s0.subst sub) (s1.subst sub)
   | .alloc s0 => .alloc (s0.subst sub)
   | .dealloc s0 => .dealloc (s0.subst sub)
   | .assign s0 s1 => .assign (s0.subst sub) (s1.subst sub)
   | .tm_pair s0 s1 => .tm_pair (s0.subst sub) (s1.subst sub)
   | .left_tm s0 => .left_tm (s0.subst sub)

   | .right_tm s0 => .right_tm (s0.subst sub)
   | .inl s0 => .inl (s0.subst sub)
   | .inr s0 => .inr (s0.subst sub)
   | .case s0 nm1 s1 nm2 s2 => .case (s0.subst sub) nm1 (s1.subst $ sub.bump #Tm) nm2 (s2.subst $ sub.bump #Tm)
   | .tapp s0 s1 => .tapp (s0.subst sub) (s1.subst $ sub.toSubst)
   | .lapp s0 s1 => .lapp (s0.subst sub) (s1.subst $ sub.toLabelSubst)
   | .rapp e0 re => .rapp (e0.subst sub) (re.subst $ sub.toRexpSubst)
   | .pack s s0 => .pack (s.subst sub.toSubst) (s0.subst sub)
   | .rpack re s0 => .rpack (re.subst $ sub.toRexpSubst) (s0.subst sub)
   | .unpack s0 nm1 nm2 s1 => .unpack (s0.subst sub) nm1 nm2 (s1.subst $ (sub.bump #Ty).bump #Tm)
   | .if_tm s0 s1 s2 => .if_tm (s0.subst sub) (s1.subst sub) (s2.subst sub)
   | .if_c s0 s1 s2 => .if_c (s0.subst sub.toLabelSubst) (s1.subst sub) (s2.subst sub)
   | .corr_case lab e => .corr_case (lab.subst sub.toLabelSubst) (e.subst sub)
   | .annot e t => .annot (e.subst sub) (t.subst $ sub.toSubst)
   | .mk_record l => .mk_record $ l.subst sub

  def tm_list.subst (l : tm_list s) (sub : TmSubst s s') : tm_list s' :=
    match l with
    | .nil => .nil
    | .cons s e l => .cons s (e.subst sub) (l.subst sub)
end


-- Down-coercions

/-

class Down (s t : Type) where
  down : s -> t

def tm_list.subst (l : tm_list s) (sub : Subst s s') : tm_list s' :=
  match l with
  | .nil => .nil
  | .cons s e l => .cons s (e.subst sub) (l.subst sub)
end

def label.downTy (l : label s.bumpTy) : label s :=
  match l with
  | .var_label s0 i => .var_label s0 i
  | .latl x => .latl x
  | .ljoin l1 l2 => .ljoin (l1.downTy) (l2.downTy)
  | .lmeet l1 l2 => .lmeet (l1.downTy) (l2.downTy)
  | .default => .default

instance : Down (label s.bumpTy) (label s) where
  down := label.downTy

instance [Down s t] : Down (List s) (List t) where
  down := fun l => l.map (Down.down ·)

def rexp.downTy (r : rexp s.bumpTy) : rexp s :=
  match r with
  | .fvar i => .fvar i
  | .var j => .var j
  | .op s r1 r2 => .op s (r1.downTy) (r2.downTy)
  | .const b => .const b
  | .tmvar j => .tmvar j

instance : Down (rexp s.bumpTy) (rexp s) where
  down := rexp.downTy

def label.downTm (l : label s.bumpTm) : label s :=
  match l with
  | .var_label s0 i => .var_label s0 i
  | .latl x => .latl x
  | .ljoin l1 l2 => .ljoin (l1.downTm) (l2.downTm)
  | .lmeet l1 l2 => .lmeet (l1.downTm) (l2.downTm)
  | .default => .default

-/


inductive Decl : ScopeMap 4 -> ScopeMap 4 -> Type where
  | Nil : Decl se se
  | DeclTy {s : ScopeMap 4} (name : Name) (ty : ty (s.restrict _)) : Decl s (s.bump #Ty)
  | DeclTm {s : ScopeMap 4} (name : Name) (tm : tm s) (ot : Option (ty (s.restrict _))) : Decl s (s.bump #Tm)
  | DeclTmAssume {s : ScopeMap 4} (name : Name) (t : ty (s.restrict _)) : Decl s (s.bump #Tm)
  | DeclLabel {s : ScopeMap 4} (name : Name) (cond_sym : cond_sym) (label : label (s.restrict _)) : Decl s (s.bump #L)
  | DeclApp : Decl se se' -> Decl se' se'' -> Decl se se''

/-

inductive Decl : ScopeEnv -> ScopeEnv -> Type where
  | Nil : Decl se se
  | DeclTy {se : ScopeEnv} (name : String) (ty : ty se.l se.r se.d se.m) : Decl se {se with d := se.d + 1}
  | DeclTm : String -> tm l r d m -> Decl se {se with m := se.m + 1}
  | DeclApp : Decl se se' -> Decl se' se'' -> Decl se se''
-/

def ty.erase_varname (t : ty s) : ty s :=
  t.subst $ ⟨fun x i =>
    match x with
    | #Ty => .var_ty "" i
    | #L => .var_label "" (i.cast (by simp))
    | #R => .var (i.cast (by simp))
  ⟩

end Owl
