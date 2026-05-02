import Lean

namespace Owl


structure Lattice where
  labels : Type
  leq    : labels -> labels -> Prop
  bot    : labels
  bot_proof : forall (l : labels), (leq bot l) = true
  join   : labels -> labels -> labels
  meet   : labels -> labels -> labels
  leq_trans : forall l1 l2 l3, leq l1 l2 -> leq l2 l3 -> leq l1 l3
  leq_refl : forall l, leq l l
  bot_all : forall l, leq bot l
  join_le : forall l1 l2 l3, leq l1 l3 -> leq l2 l3 -> leq (join l1 l2) l3

inductive LabelTm where
  | atom : String -> LabelTm
  | and : LabelTm -> LabelTm -> LabelTm
  | or : LabelTm -> LabelTm -> LabelTm
  | bot : LabelTm
  deriving BEq, Repr, Lean.ToExpr

def LabelTm.interp (t : LabelTm) (p : String -> Bool) : Bool :=
  match t with
  | .atom x => p x
  | .and x y => x.interp p && y.interp p
  | .or x y => x.interp p || y.interp p
  | .bot => true

-- l2 implies l1
def LabelTm.leq (l1 : LabelTm) (l2 : LabelTm) :=
  forall p, (! l2.interp p) || l1.interp p

def L : Lattice := {
    labels := LabelTm,
    leq := LabelTm.leq,
    bot := .bot,
    bot_proof := by
      intros l
      simp [LabelTm.leq]
      simp [LabelTm.interp]
    join := .and,
    meet := .or,
    leq_trans := by
      intros l1 l2 l3
      unfold LabelTm.leq
      intros h1 h2 p
      grind
    leq_refl := by
      unfold LabelTm.leq
      grind
    bot_all := by
      unfold LabelTm.leq
      simp [LabelTm.interp]
    join_le := by
      intros l1 l2 l3 h1 h2
      simp [LabelTm.leq, LabelTm.interp] at *
      intros
      grind
}


instance : Lean.ToExpr L.labels := by
  unfold L
  simp
  infer_instance

instance : Repr L.labels := by
  unfold L
  simp
  infer_instance

def lattice_leq_trans : forall {l1 l2 l3}, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 :=
  fun {l1 l2 l3} =>
    L.leq_trans l1 l2 l3

grind_pattern lattice_leq_trans => L.leq l1 l2, L.leq l2 l3

def lattice_leq_refl : forall {l}, L.leq l l := fun {l} => L.leq_refl l

grind_pattern lattice_leq_refl => L.leq l l

def lattice_bot_all : forall {l}, L.leq L.bot l := fun {l} => L.bot_all l

grind_pattern lattice_bot_all => L.leq L.bot l

def lattice_join_bot : forall {l}, L.leq (L.join L.bot l) l := by
  intros
  apply L.join_le
  grind
  grind

grind_pattern lattice_join_bot => (L.join L.bot l)

@[simp]
theorem leq_bot : L.leq L.bot l := by
  grind

abbrev Lcarrier : Type := L.labels

instance : BEq Lcarrier := by
  unfold Lcarrier
  simp [L]
  infer_instance


structure opaqueSyntax where
  inner : Lean.Syntax

instance : Repr opaqueSyntax where
  reprPrec _ _ := f!"<syntax>"

structure Scope where
  nLbl : Nat
  nRef : Nat
  nTy : Nat
  nTm : Nat
  deriving BEq, Lean.ToExpr

abbrev Scope.empty : Scope := {
  nLbl := 0
  nRef := 0
  nTy := 0
  nTm := 0
}

abbrev Scope.withoutTms (s : Scope) : Scope := { s with nTm := 0 }

class Scope.closedTm (s : Scope) where
  h : s.nTm = 0


abbrev Scope.bumpRef (s : Scope) := { s with nRef := s.nRef + 1 }
abbrev Scope.bumpTy (s : Scope) := { s with nTy := s.nTy + 1 }
abbrev Scope.bumpLbl (s : Scope) := { s with nLbl := s.nLbl + 1 }
abbrev Scope.bumpTm (s : Scope) := { s with nTm := s.nTm + 1 }

structure Scope.renaming (s s' : Scope) where
  renameLbl : Fin s.nLbl -> Fin s'.nLbl
  renameRef : Fin s.nRef -> Fin s'.nRef
  renameTy : Fin s.nTy -> Fin s'.nTy
  renameTm : Fin s.nTm -> Fin s'.nTm

def up_ren (xi : Fin m -> Fin n) : Fin (m + 1) -> Fin (n + 1) :=
  Fin.cases 0 (Fin.succ ∘ xi)

abbrev Scope.renaming.bumpRef {s : Scope} (r : s.renaming s') : s.bumpRef.renaming s'.bumpRef := {
  r with
    renameRef := up_ren r.renameRef
}

abbrev Scope.renaming.bumpTy {s : Scope} (r : s.renaming s') : s.bumpTy.renaming s'.bumpTy := {
  r with
    renameTy := up_ren r.renameTy
}

abbrev Scope.renaming.bumpLbl {s : Scope} (r : s.renaming s') : s.bumpLbl.renaming s'.bumpLbl := {
  r with
    renameLbl := up_ren r.renameLbl
}

abbrev Scope.renaming.bumpTm {s : Scope} (r : s.renaming s') : s.bumpTm.renaming s'.bumpTm := {
  r with
    renameTm := up_ren r.renameTm
}

abbrev Scope.liftRef {s : Scope} : s.renaming s.bumpRef := {
  renameLbl := id
  renameTy := id
  renameRef := Fin.succ
  renameTm := id
}

abbrev Scope.liftTy {s : Scope} : s.renaming s.bumpTy := {
  renameLbl := id
  renameTy := Fin.succ
  renameRef := id
  renameTm := id
}

abbrev Scope.liftLbl {s : Scope} : s.renaming s.bumpLbl := {
  renameLbl := Fin.succ
  renameTy := id
  renameRef := id
  renameTm := id
}

abbrev Scope.liftTm {s : Scope} : s.renaming s.bumpTm := {
  renameLbl := id
  renameTy := id
  renameRef := id
  renameTm := Fin.succ
}

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


inductive label : Scope -> Type where
| var_label : String -> Fin s.nLbl -> label s
| latl : Lcarrier -> label s
| ljoin : label s -> label s -> label s
| lmeet : label s -> label s -> label s
| default : label s
deriving Repr, BEq, Lean.ToExpr

def label.downRef {s:Scope} (l : label s.bumpRef) : label s :=
  match l with
  | .var_label s0 i => .var_label s0 i
  | .latl x => .latl x
  | .ljoin l1 l2 => .ljoin (l1.downRef) (l2.downRef)
  | .lmeet l1 l2 => .lmeet (l1.downRef) (l2.downRef)
  | .default => .default


inductive corruption : Scope -> Type where
| corr : label s -> corruption s
| not_corr : label s -> corruption s
deriving Repr, BEq, Lean.ToExpr

inductive constr  : Scope -> Type where
| condition : cond_sym -> label s -> label s -> constr s
deriving Repr, BEq, Lean.ToExpr

abbrev GUId := Nat


deriving instance BEq, Lean.ToExpr for String.Pos.Raw
deriving instance BEq, Lean.ToExpr for Substring.Raw
deriving instance BEq, Lean.ToExpr for Lean.SourceInfo
deriving instance BEq, Lean.ToExpr for Lean.Syntax
deriving instance BEq, Lean.ToExpr for Owl.opaqueSyntax


inductive rexp : Scope -> Type where
  | fvar : Lean.Name -> rexp s
  | var : Fin s.nRef -> rexp s
  | op : String -> rexp s -> rexp s -> rexp s
  | tmvar : Fin s.nTm -> rexp s
  | const : String -> rexp s
deriving Repr, BEq, Lean.ToExpr



inductive prop : Scope -> Type where
  | peq : rexp s -> rexp s -> prop s
  | pand : prop s -> prop s -> prop s
  | por : prop s -> prop s -> prop s
  | pimpl : prop s -> prop s -> prop s
  | pnot : prop s -> prop s
  | pall : prop s.bumpRef -> prop s
  deriving Repr, BEq, Lean.ToExpr




inductive ty : Scope -> Type where
| var_ty : Fin s.nTy -> ty s
| Any : ty s
| Unit : ty s
| RData : label s -> rexp s -> ty s
| Data : label s -> ty s
| Ref : ty s -> ty s
| arr : ty s -> ty s -> ty s
| union : ty s -> ty s -> ty s
| inter : ty s -> ty s -> ty s
| prod : ty s -> ty s -> ty s
| sum : ty s -> ty s -> ty s
| all : ty s -> ty s.bumpTy -> ty s
| ex : ty s -> ty s.bumpTy -> ty s
| ex_r : ty s.bumpRef -> ty s
| all_r : ty s.bumpRef -> ty s
| all_l : cond_sym -> label s -> ty s.bumpLbl -> ty s
| t_if : label s -> ty s -> ty s -> ty s
| refined : ty s -> prop s -> ty s
| Public : ty s
| default : ty s
| admit : ty s
deriving Repr, BEq, Lean.ToExpr



mutual

  inductive tm : Scope -> Type where
   | mk : opaqueSyntax -> tmX s -> tm s
   deriving Repr, Lean.ToExpr

inductive tmX : Scope -> Type where
| admit : tmX s
| var_tm : Fin s.nTm -> tmX s
| error : tmX s
| skip : tmX s
| bitstring : String -> tmX s
| loc : Nat -> tmX s
| fixlam : String -> tm (s.bumpTm.bumpTm) -> tmX s
| tlet : tm s -> tm s.bumpTm -> tmX s
| union_elim : tm s -> tm s.bumpTm -> tmX s
| tlam : tm s.bumpTy -> tmX s
| rlam : tm s.bumpRef -> tmX s
| l_lam : tm s.bumpLbl -> tmX s
| Op : String -> tm s -> tm s -> tmX s
| zero : tm s -> tmX s
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
    tm s.bumpTm -> tm s.bumpTm -> tmX s
| tapp : tm s -> ty s -> tmX s
| lapp : tm s -> label s -> tmX s
| rapp : tm s -> rexp s -> tmX s
| pack : ty s -> tm s -> tmX s
| rpack : rexp s -> tm s -> tmX s
| unpack : tm s -> tm s.bumpTy.bumpTm -> tmX s
| if_tm :
    tm s ->
    tm s -> tm s -> tmX s
| if_c :
    label s -> tm s -> tm s -> tmX s
| sync : tm s -> tmX s
| corr_case : label s -> tm s -> tmX s
| annot : tm s -> ty s -> tmX s
| default : tmX s
deriving Repr, Lean.ToExpr

end

def rexp.free (i : Fin s.nRef) (re : rexp s) :=
  match re with
  | .fvar _ => true
  | .var j      => i != j
  | .op _ r1 r2 => rexp.free i r1 && rexp.free i r2
  | .const _    => true
  | .tmvar _ => true

@[simp]
def prop.rfree  (p : prop s) (i : Fin s.nRef) : Bool :=
  match p with
  | .peq re1 re2 => rexp.free i re1 && rexp.free i re2
  | .pand p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .por p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .pimpl p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .pnot p1 => prop.rfree p1 i
  | .pall p0 => prop.rfree p0 (Fin.succ i)


@[simp]
def ty.r_free (t : ty s) (i : Fin s.nRef) : Bool :=
  match t with
| .admit => true
| .var_ty _ => true
| .Any => true
| .refined t0 p => t0.r_free i && p.rfree i
| .Unit => true
| .RData _ re => rexp.free i re
| .Data _ => true
| .Ref t => t.r_free i
| .arr t1 t2 => t1.r_free i && t2.r_free i
| .union t1 t2 => t1.r_free i && t2.r_free i
| .inter t1 t2 => t1.r_free i && t2.r_free i
| .prod t1 t2 => t1.r_free i && t2.r_free i
| .sum t1 t2 => t1.r_free i && t2.r_free i
| .all t1 t2 => t1.r_free i && t2.r_free i
| .ex t1 t2 => t1.r_free i && t2.r_free i
| .ex_r t0 => t0.r_free (Fin.succ i)
| .all_r t0 => t0.r_free (Fin.succ i)
| .all_l _ _ t => t.r_free i
| .t_if _ t1 t2 => t1.r_free i && t2.r_free i
| .Public => true
| .default => true



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
  | .var_label n s0 => label.var_label n (ren.renameLbl s0)
  | .latl s0 => label.latl s0
  | .ljoin s0 s1 => label.ljoin (s0.rename ren) (s1.rename ren)
  | .lmeet s0 s1 => label.lmeet (s0.rename ren) (s1.rename ren)
  | .default => .default

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


def rexp.rename (r : rexp s) (ren : s.renaming s')
  : rexp s' :=
    match r with
    | .fvar i => .fvar i
    | .var j => .var (ren.renameRef j)
    | .op s r1 r2 => .op s (r1.rename ren) (r2.rename ren)
    | .const b => .const b
    | .tmvar j => .tmvar (ren.renameTm j)

def prop.rename (p : prop s) (ren : s.renaming s') : prop s' :=
  match p with
  | .peq re1 re2 => .peq (re1.rename ren) (re2.rename ren)
  | .pand p1 p2 => .pand (p1.rename ren) (p2.rename ren)
  | .por p1 p2 => .por (p1.rename ren) (p2.rename ren)
  | .pimpl p1 p2 => .pimpl (p1.rename ren) (p2.rename ren)
  | .pnot p1 => .pnot (p1.rename ren)
  | .pall p => .pall (p.rename ren.bumpRef)


@[simp]
def ty.rename (t : ty s) (ren : s.renaming s') : ty s' :=
  match t with
  | .admit => .admit
  | .var_ty s0 => .var_ty (ren.renameTy s0)
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (s0.rename ren) (re.rename ren)
  | .Data s0 => .Data (s0.rename ren)
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
      .refined (t.rename ren) (p.rename ren)
  | .sum s0 s1 =>
      .sum (s0.rename ren) (s1.rename ren)
  | .all s0 s1 =>
      .all (s0.rename ren)
           (s1.rename ren.bumpTy)
  | .ex s0 s1 =>
      .ex (s0.rename ren)
           (s1.rename ren.bumpTy)
  | .ex_r t0 => .ex_r (t0.rename ren.bumpRef)
  | .all_r t0 => .all_r (t0.rename ren.bumpRef)
  | .all_l s0 s1 s2 =>
      .all_l s0 (s1.rename ren)
        (s2.rename ren.bumpLbl)
  | .t_if s0 s1 s2 =>
      .t_if (s0.rename ren) (s1.rename ren)
        (s2.rename ren)
  | .Public => .Public
  | .default => .default


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
  | .var_tm s0 => .var_tm (ren.renameTm s0)
  | .error => .error
  | .skip => .skip
  | .bitstring s0 => .bitstring s0
  | .loc s0 => .loc s0
  | .fixlam nm s0 =>
      .fixlam nm
        (s0.rename ren.bumpTm.bumpTm)
  | .tlam s0 =>
      .tlam (s0.rename ren.bumpTy)
  | .rlam s0 =>
    .rlam
        (s0.rename ren.bumpRef)
  | .tlet e1 e2 =>
    .tlet (e1.rename ren)
          (e2.rename ren.bumpTm)
  | .union_elim e1 e2 =>
    .union_elim (e1.rename ren)
                (e2.rename ren.bumpTm)
  | .l_lam s0 =>
      .l_lam
        (s0.rename ren.bumpLbl)
  | .Op s0 s1 s2 =>
      .Op s0 (s1.rename ren)
        (s2.rename ren)
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
  | .case s0 s1 s2 =>
      .case (s0.rename ren)
            (s1.rename ren.bumpTm)
            (s2.rename ren.bumpTm)
  | .tapp s0 s1 =>
      .tapp (s0.rename ren)
        (s1.rename ren)
  | .lapp s0 s1 =>
      .lapp (s0.rename ren)
            (s1.rename ren)
  | .rapp e0 re =>
      .rapp (e0.rename ren)
            (re.rename ren)
  | .pack s s0 => .pack
    (s.rename ren)
    (s0.rename ren)
  | .rpack re t0 => .rpack (re.rename ren) (t0.rename ren)
  | .unpack s0 s1 =>
      .unpack (s0.rename ren)
              (s1.rename ren.bumpTy.bumpTm)
  | .if_tm s0 s1 s2 =>
      .if_tm (s0.rename ren)
             (s1.rename ren) (s2.rename ren)
  | .if_c s0 s1 s2 =>
      .if_c (s0.rename ren)
            (s1.rename ren)
            (s2.rename ren)
  | .sync s0 => .sync (s0.rename ren)
  | .corr_case lab e => .corr_case (lab.rename ren) (e.rename ren)
  | .annot e t => .annot (e.rename ren) (t.rename ren)
  | .default => .default
end


structure Scope.subst (s s' : Scope) where
  substLbl : Fin s.nLbl -> label s'
  substRef : Fin s.nRef -> rexp s'
  substTy : Fin s.nTy -> ty s'
  substTm : Fin s.nTm -> rexp s'

abbrev mapM [Monad m] (c : m a) (f : a -> b) : m b :=
  c >>= fun x => pure (f x)

abbrev Scope.subst.bumpRef {s : Scope} (sub : s.subst s') : s.bumpRef.subst s'.bumpRef := {
  substLbl := fun i => (sub.substLbl i).rename Scope.liftRef,
  substRef := fun i => Fin.cases (.var 0) (fun j => (sub.substRef j).rename Scope.liftRef) i,
  substTy := fun i => (sub.substTy i).rename Scope.liftRef,
  substTm := fun i => (sub.substTm i).rename Scope.liftRef
}

abbrev Scope.subst.downRef {s : Scope} (r : rexp s) : s.bumpRef.subst s := {
  substLbl := fun i => .var_label "_" i,
  substRef := fun i => Fin.cases r (fun j => .var j) i,
  substTy := fun i => .var_ty i,
  substTm := fun i => .tmvar i
}

abbrev Scope.subst.bumpTy {s : Scope} (sub : s.subst s') : s.bumpTy.subst s'.bumpTy := {
  substLbl := fun i => (sub.substLbl i).rename Scope.liftTy,
  substRef := fun i => (sub.substRef i).rename Scope.liftTy,
  substTy := fun i => Fin.cases (.var_ty 0) (fun j => (sub.substTy j).rename Scope.liftTy) i,
  substTm := fun i => (sub.substTm i).rename Scope.liftTy
}

abbrev Scope.subst.bumpLbl {s : Scope} (sub : s.subst s') : s.bumpLbl.subst s'.bumpLbl := {
  substLbl := fun i => Fin.cases (.var_label "_" 0) (fun j => (sub.substLbl j).rename Scope.liftLbl) i,
  substRef := fun i => (sub.substRef i).rename Scope.liftLbl,
  substTy := fun i => (sub.substTy i).rename Scope.liftLbl,
  substTm := fun i => (sub.substTm i).rename Scope.liftLbl
}

abbrev Scope.subst.bumpTm {s : Scope} (sub : s.subst s') : s.bumpTm.subst s'.bumpTm := {
  substLbl := fun i => (sub.substLbl i).rename Scope.liftTm,
  substRef := fun i => (sub.substRef i).rename Scope.liftTm,
  substTy := fun i => (sub.substTy i).rename Scope.liftTm,
  substTm := fun i => Fin.cases (.tmvar 0) (fun j => (sub.substTm j).rename Scope.liftTm) i
}


@[simp]
def label.subst (l : label s) (sub : s.subst s') : label s' :=
  match l with
  | .var_label _ s0 => sub.substLbl s0
  | .latl s0 => .latl s0
  | .ljoin s0 s1 =>
      let s0' := s0.subst sub
      let s1' := s1.subst sub
      .ljoin s0' s1'
  | .lmeet s0 s1 =>
      let s0' := s0.subst sub
      let s1' := s1.subst sub
      .lmeet s0' s1'
  | .default => .default

@[simp]
def corruption.subst (c : corruption s) (sub : s.subst s') : corruption s' :=
  match c with
  | .corr l1 =>
      let l1' := l1.subst sub
      .corr l1'
  | .not_corr l1 =>
      let l1' := l1.subst sub
      .not_corr l1'

@[simp]
def constr.subst (c : constr s) (sub : s.subst s') : constr s' :=
  match c with
  | .condition s0 s1 s2 =>
      let s1' := s1.subst sub
      let s2' := s2.subst sub
      .condition s0 s1' s2'


def rexp.subst (r : rexp s) (sub : s.subst s') : rexp s' :=
  match r with
  | .fvar i => .fvar i
  | .var j => sub.substRef j
  | .op s r1 r2 =>
      let r1' := r1.subst sub
      let r2' := r2.subst sub
      .op s r1' r2'
  | .const b => .const b
  | .tmvar j => sub.substTm j

def prop.subst (p : prop s) (sub : s.subst s') : prop s' :=
  match p with
  | .peq re1 re2 => .peq (re1.subst sub) (re2.subst sub)
  | .pand p1 p2 => .pand (p1.subst sub) (p2.subst sub)
  | .por p1 p2 => .por (p1.subst sub) (p2.subst sub)
  | .pimpl p1 p2 => .pimpl (p1.subst sub) (p2.subst sub)
  | .pnot p1 => .pnot (p1.subst sub)
  | .pall p => .pall (p.subst sub.bumpRef)


@[simp]
def ty.subst (t : ty s) (sub : s.subst s') : ty s' :=
  match t with
  | .admit => .admit
  | .var_ty s0 => sub.substTy s0
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (s0.subst sub) (re.subst sub)
  | .Data s0 => .Data (s0.subst sub)
  | .Ref s0 => .Ref (s0.subst sub)
  | .refined t p => .refined (t.subst sub) (p.subst sub)
  | .arr s0 s1 => .arr (s0.subst sub) (s1.subst sub)
  | .union s0 s1 => .union (s0.subst sub) (s1.subst sub)
  | .inter s0 s1 => .inter (s0.subst sub) (s1.subst sub)
  | .prod s0 s1 => .prod (s0.subst sub) (s1.subst sub)
  | .sum s0 s1 => .sum (s0.subst sub) (s1.subst sub)
  | .all s0 s1 =>
      .all (s0.subst sub) (s1.subst sub.bumpTy)
  | .ex s0 s1 =>
      .ex (s0.subst sub) (s1.subst sub.bumpTy)
  | .ex_r t0 =>
      .ex_r (t0.subst sub.bumpRef)
  | .all_r t0 =>
      .all_r (t0.subst sub.bumpRef)
  | .all_l s0 s1 s2 =>
      .all_l s0 (s1.subst sub) (s2.subst sub.bumpLbl)
  | .t_if s0 s1 s2 =>
      .t_if (s0.subst sub) (s1.subst sub) (s2.subst sub)
  | .Public => .Public
  | .default => .default



/-

inductive Decl : ScopeEnv -> ScopeEnv -> Type where
  | Nil : Decl se se
  | DeclTy {se : ScopeEnv} (name : String) (ty : ty se.l se.r se.d se.m) : Decl se {se with d := se.d + 1}
  | DeclTm : String -> tm l r d m -> Decl se {se with m := se.m + 1}
  | DeclApp : Decl se se' -> Decl se' se'' -> Decl se se''
-/


end Owl
