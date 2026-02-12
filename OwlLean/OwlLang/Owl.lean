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


inductive cond_sym : Type
| leq : cond_sym
| geq : cond_sym
| gt : cond_sym
| lt : cond_sym
| nleq : cond_sym
| ngeq : cond_sym
| ngt : cond_sym
| nlt : cond_sym
deriving Repr, DecidableEq


inductive label : Nat -> Type where
| var_label : String -> Fin n -> label n
| latl : Lcarrier -> label n
| ljoin : label n -> label n -> label n
| lmeet : label n -> label n -> label n
| default : label n
deriving Repr, BEq

inductive corruption : Nat -> Type where
| corr : label n -> corruption n
| not_corr : label n -> corruption n
deriving Repr, BEq

inductive constr (n_label : Nat) : Type where
| condition : cond_sym -> label n_label -> label n_label -> constr n_label
deriving Repr, BEq

inductive rexp : Nat -> Type where
  | var : Fin r -> rexp r
  | op : String -> rexp r -> rexp r -> rexp r
  | const : String -> rexp r
deriving Repr, BEq

def rexp.free (i : Fin r) (re : rexp r) :=
  match re with
  | .var j      => i != j
  | .op _ r1 r2 => rexp.free i r1 && rexp.free i r2
  | .const _    => true

def rexp.down (re : rexp (r + 1)) (i : Fin (r + 1)) (h : re.free i) : rexp r :=
  match re with
  | .var j =>
    if h2 : j < i then .var ⟨j.val, by omega⟩
      else .var (j.pred (by
        simp [free] at h;
        have: j > i := by omega
        cases i
        cases j
        simp at *
        omega))
  | .op s r1 r2 => .op s (r1.down i (by grind [free])) (r2.down i (by grind [free]))
  | .const i => .const i

inductive prop : Nat -> Type where
  | peq : rexp n -> rexp n -> prop n
  | pand : prop n -> prop n -> prop n
  | por : prop n -> prop n -> prop n
  | pimpl : prop n -> prop n -> prop n
  | pnot : prop n -> prop n
  | pall : prop (n + 1) -> prop n
  deriving Repr, BEq



@[simp]
def prop.rfree {n : Nat} (p : prop n) (i : Fin n) : Bool :=
  match p with
  | .peq re1 re2 => rexp.free i re1 && rexp.free i re2
  | .pand p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .por p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .pimpl p1 p2 => prop.rfree p1 i && prop.rfree p2 i
  | .pnot p1 => prop.rfree p1 i
  | .pall p0 => prop.rfree p0 (Fin.succ i)

@[simp]
def prop.down (p : prop (n + 1)) (i : Fin (n + 1)) (h : p.rfree i) :prop n :=
match p with
| .peq re1 re2 =>
    .peq (rexp.down re1 i (by simp [rfree] at h; apply And.left h)) (rexp.down re2 i (by simp [rfree] at h; apply And.right h))
| .pand p1 p2 =>
    .pand (prop.down p1 i (by simp [rfree] at h; apply And.left h)) (prop.down p2 i (by simp [rfree] at h; apply And.right h))
| .por p1 p2 =>
    .por (prop.down p1 i (by simp [rfree] at h; apply And.left h)) (prop.down p2 i (by simp [rfree] at h; apply And.right h))
| .pimpl p1 p2 =>
    .pimpl (prop.down p1 i (by simp [rfree] at h; apply And.left h)) (prop.down p2 i (by simp [rfree] at h; apply And.right h))
| .pnot p0 =>
    .pnot (prop.down p0 i (by exact h))
| .pall p0 =>
    .pall (prop.down p0 (Fin.succ i) (by simp [rfree] at h; exact h))


inductive ty : Nat -> Nat -> Nat -> Type where
| var_ty : Fin n_ty -> ty n_label n_ref n_ty
| Any : ty n_label n_ref n_ty
| Unit : ty n_label n_ref n_ty
| RData : label n_label -> rexp n_ref -> ty n_label n_ref n_ty
| Data : label n_label -> ty n_label n_ref n_ty
| Ref : ty n_label n_ref n_ty -> ty n_label n_ref n_ty
| arr : ty n_label n_ref n_ty -> ty n_label n_ref n_ty -> ty n_label n_ref n_ty
| prod : ty n_label n_ref n_ty -> ty n_label n_ref n_ty -> ty n_label n_ref n_ty
| sum : ty n_label n_ref n_ty -> ty n_label n_ref n_ty -> ty n_label n_ref n_ty
| all : ty n_label n_ref n_ty -> ty n_label n_ref (n_ty + 1) -> ty n_label n_ref n_ty
| ex : ty n_label n_ref n_ty -> ty n_label n_ref (n_ty + 1) -> ty n_label n_ref n_ty
| ex_r : ty n_label (n_ref + 1) n_ty -> ty n_label n_ref n_ty
| all_r : ty n_label (n_ref + 1) n_ty -> ty n_label n_ref n_ty
| all_l : cond_sym -> label n_label -> ty (n_label + 1) n_ref n_ty -> ty n_label n_ref n_ty
| t_if : label n_label -> ty n_label n_ref n_ty -> ty n_label n_ref n_ty -> ty n_label n_ref n_ty
| refined : ty n_label n_ref n_ty -> prop n_ref -> ty n_label n_ref n_ty
| Public : ty n_label n_ref n_ty
| default : ty n_label n_ref n_ty
deriving Repr, BEq

@[simp]
def ty.r_free {l r d : Nat} (i : Fin r) : ty l r d → Bool
| .var_ty _ => true
| .Any => true
| .refined t0 p => t0.r_free i && p.rfree i
| .Unit => true
| .RData _ re => rexp.free i re
| .Data _ => true
| .Ref t => ty.r_free i t
| .arr t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .prod t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .sum t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .all t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .ex t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .ex_r t0 => ty.r_free (Fin.succ i) t0
| .all_r t0 => ty.r_free (Fin.succ i) t0
| .all_l _ _ t => ty.r_free i t
| .t_if _ t1 t2 => ty.r_free i t1 && ty.r_free i t2
| .Public => true
| .default => true

def ty.down (t : ty l (r + 1) d) (i : Fin (r + 1)) (h : t.r_free i) : ty l r d :=
match t with
| .var_ty i => .var_ty i
| .Any => .Any
| .Unit => .Unit
| .RData l re => .RData l (re.down i h)
| .Data l => .Data l
| .Ref t => .Ref (t.down i h)
| .refined t0 p => .refined (t0.down i (by grind [r_free])) (p.down i (by grind [r_free]))
| .arr t1 t2 => .arr (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .prod t1 t2 => .prod (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .sum t1 t2 => .sum (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .all t1 t2 => .all (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .ex t1 t2 => .ex (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .ex_r t1 => .ex_r (t1.down i.succ (by grind [r_free]))
| .all_r t1 => .all_r (t1.down i.succ (by grind [r_free]))
| .all_l cs l t0 => .all_l cs l (t0.down i (by grind [r_free]))
| .t_if l t1 t2 => .t_if l (t1.down i (by grind [r_free])) (t2.down i (by grind [r_free]))
| .Public => .Public
| .default => .Public


inductive Dist (a : Type) : Type where
| ret  : a -> Dist a
| flip : (Bool -> Dist a) → Dist a


mutual
  inductive tm : Nat -> Nat -> Nat -> Nat -> Type where
   | mk : opaqueSyntax -> tmX l d m r -> tm l d m r
   deriving Repr

inductive tmX : Nat -> Nat -> Nat -> Nat -> Type where
| var_tm : Fin n_tm -> tmX n_label n_ref n_ty n_tm
| error : tmX n_label n_ref n_ty n_tm
| skip : tmX n_label n_ref n_ty n_tm
| bitstring : String -> tmX n_label n_ref n_ty n_tm
| loc : Nat -> tmX n_label n_ref n_ty n_tm
| fixlam : String -> tm n_label n_ref n_ty ((n_tm + 1) + 1) -> tmX n_label n_ref n_ty n_tm
| letr : tm n_label n_ref n_ty n_tm -> tm n_label (n_ref + 1) n_ty (n_tm + 1) -> tmX n_label n_ref n_ty n_tm
| tlam : tm n_label n_ref (n_ty + 1) n_tm -> tmX n_label n_ref n_ty n_tm
| rlam : tm n_label (n_ref + 1) n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| l_lam : tm (n_label + 1) n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| Op : String -> tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| zero : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| app : tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| alloc : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| dealloc : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| assign : tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| tm_pair : tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| left_tm : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| right_tm : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| inl : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| inr {n_label n_ref n_ty n_tm} : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| case :
    tm n_label n_ref n_ty n_tm ->
    tm n_label n_ref n_ty (n_tm + 1) -> tm n_label n_ref n_ty (n_tm + 1) -> tmX n_label n_ref n_ty n_tm
| tapp : tm n_label n_ref n_ty n_tm -> ty n_label n_ref n_ty -> tmX n_label n_ref n_ty n_tm
| lapp : tm n_label n_ref n_ty n_tm -> label n_label -> tmX n_label n_ref n_ty n_tm
| rapp : tm n_label n_ref n_ty n_tm -> rexp n_ref -> tmX n_label n_ref n_ty n_tm
| pack : ty n_label n_ref n_ty -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| rpack : rexp n_ref -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| unpack : tm n_label n_ref n_ty n_tm -> tm n_label n_ref (n_ty + 1) (n_tm + 1) -> tmX n_label n_ref n_ty n_tm
| if_tm :
    tm n_label n_ref n_ty n_tm ->
    tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| if_c :
    label n_label -> tm n_label n_ref n_ty n_tm -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| sync : tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| corr_case : label n_label -> tm n_label n_ref n_ty n_tm -> tmX n_label n_ref n_ty n_tm
| annot : tm n_label n_ref n_ty n_tm -> ty n_label n_ref n_ty -> tmX n_label n_ref n_ty n_tm
| default : tmX n_label n_ref n_ty n_tm
deriving Repr

end

deriving instance Lean.ToExpr for Owl.Lcarrier
deriving instance Lean.ToExpr for Owl.label
deriving instance Lean.ToExpr for Owl.corruption
deriving instance Lean.ToExpr for Owl.cond_sym
deriving instance Lean.ToExpr for Owl.constr
deriving instance Lean.ToExpr for Owl.rexp
deriving instance Lean.ToExpr for Owl.prop
deriving instance Lean.ToExpr for Owl.ty

@[always_inline]
abbrev tm.get (t : tm l d m r) : tmX l d m r :=
  match t with
  | .mk _ v => v

@[simp]
def tm.mkD (t : tmX l d m r) : tm l d m r :=
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

def up_ren (xi : ren m n) : ren (m + 1) (n + 1) :=
  cons var_zero (funcomp shift xi)

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
def ren_label
  (xi_label : Fin m_label → Fin n_label)
  (s : label m_label) : label n_label :=
  match s with
  | .var_label n s0 => label.var_label n (xi_label s0)
  | .latl s0 => label.latl s0
  | .ljoin s0 s1 => label.ljoin (ren_label xi_label s0) (ren_label xi_label s1)
  | .lmeet s0 s1 => label.lmeet (ren_label xi_label s0) (ren_label xi_label s1)
  | .default => .default

def ren_constr
  (xi_label : Fin m_label -> Fin n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | .condition s0 s1 s2 => .condition s0 (ren_label xi_label s1) (ren_label xi_label s2)

def ren_corruption
  (xi_label : Fin m_label → Fin n_label)
  (s : corruption m_label) : corruption n_label :=
  match s with
  | .corr l1 => .corr (ren_label xi_label l1)
  | .not_corr l1 => .not_corr (ren_label xi_label l1)


def ren_rexp (xi_ref : Fin m_ref -> Fin n_ref)
  (r : rexp m_ref) : rexp n_ref :=
    match r with
    | .var j => .var (xi_ref j)
    | .op s r1 r2 => .op s (ren_rexp xi_ref r1) (ren_rexp xi_ref r2)
    | .const b => .const b

def ren_prop (xi_ref : Fin m_ref -> Fin n_ref)
  (p : prop m_ref) : prop n_ref :=
  match p with
  | .peq re1 re2 => .peq (ren_rexp xi_ref re1) (ren_rexp xi_ref re2)
  | .pand p1 p2 => .pand (ren_prop xi_ref p1) (ren_prop xi_ref p2)
  | .por p1 p2 => .por (ren_prop xi_ref p1) (ren_prop xi_ref p2)
  | .pimpl p1 p2 => .pimpl (ren_prop xi_ref p1) (ren_prop xi_ref p2)
  | .pnot p1 => .pnot (ren_prop xi_ref p1)
  | .pall p => .pall (ren_prop (up_ren xi_ref) p)


@[simp]
def ren_ty
(xi_label : Fin m_label -> Fin n_label)
(xi_ref : Fin m_ref -> Fin n_ref )
(xi_ty : Fin m_ty -> Fin n_ty)
(s : ty m_label m_ref m_ty )  : ty n_label n_ref n_ty :=
  match s with
  | .var_ty s0 => .var_ty (xi_ty s0)
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (ren_label xi_label s0) (ren_rexp xi_ref re)
  | .Data s0 => .Data (ren_label xi_label s0)
  | .Ref s0 => .Ref (ren_ty xi_label xi_ref xi_ty s0)
  | .arr s0 s1 =>
      .arr (ren_ty xi_label xi_ref xi_ty s0) (ren_ty xi_label xi_ref xi_ty s1)
  | .prod s0 s1 =>
      .prod (ren_ty xi_label xi_ref xi_ty s0) (ren_ty xi_label xi_ref xi_ty s1)
  | .refined t p =>
      .refined (ren_ty xi_label xi_ref xi_ty t) (ren_prop xi_ref p)
  | .sum s0 s1 =>
      .sum (ren_ty xi_label xi_ref xi_ty s0) (ren_ty xi_label xi_ref xi_ty s1)

  | .all s0 s1 =>
      .all (ren_ty xi_label xi_ref xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) xi_ref (upRen_ty_ty xi_ty) s1)
  | .ex s0 s1 =>
      .ex (ren_ty xi_label xi_ref xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) xi_ref (upRen_ty_ty xi_ty) s1)
  | .ex_r t0 => .ex_r (ren_ty xi_label (up_ren xi_ref) xi_ty t0)
  | .all_r t0 => .all_r (ren_ty xi_label (up_ren xi_ref) xi_ty t0)
  | .all_l s0 s1 s2 =>
      .all_l s0 (ren_label xi_label s1)
        (ren_ty (upRen_label_label xi_label) xi_ref (upRen_label_ty xi_ty) s2)
  | .t_if s0 s1 s2 =>
      .t_if (ren_label xi_label s0) (ren_ty xi_label xi_ref xi_ty s1)
        (ren_ty xi_label xi_ref xi_ty s2)
  | .Public => .Public
  | .default => .default

@[simp]
def upRen_tm_label (xi : Fin m -> Fin n) :
  Fin m -> Fin n :=
    xi

@[simp]
def upRen_tm_ty (xi : Fin m -> Fin n) : Fin m -> Fin n :=
    xi

@[simp]
def upRen_tm_tm (xi : Fin m -> Fin n) :
  Fin (m + 1) -> Fin (n + 1) :=
    (up_ren xi)

@[simp]
def upRen_ty_tm (xi : Fin m -> Fin n) : Fin m -> Fin n :=
    xi

@[simp]
def upRen_label_tm (xi : Fin m -> Fin n) :
  Fin m -> Fin n :=
    xi

mutual

def ren_tm
(xi_label : Fin m_label -> Fin n_label)
(xi_ref : Fin m_ref -> Fin n_ref)
(xi_ty : Fin m_ty -> Fin n_ty)
(xi_tm : Fin m_tm -> Fin n_tm)

(s : tm m_label m_ref m_ty m_tm ) :
tm n_label n_ref n_ty n_tm :=
  match s with
  | .mk stx inner => .mk stx (ren_tmX xi_label xi_ref xi_ty xi_tm inner)


def ren_tmX
(xi_label : Fin m_label -> Fin n_label)
(xi_ref : Fin m_ref -> Fin n_ref)

(xi_ty : Fin m_ty -> Fin n_ty)
(xi_tm : Fin m_tm -> Fin n_tm)
(s : tmX m_label m_ref m_ty m_tm ) :
tmX n_label n_ref n_ty n_tm :=
  match s with
  | .var_tm s0 => .var_tm (xi_tm s0)
  | .error => .error
  | .skip => .skip
  | .bitstring s0 => .bitstring s0
  | .loc s0 => .loc s0
  | .fixlam nm s0 =>
      .fixlam nm
        (ren_tm (upRen_tm_label (upRen_tm_label xi_label))
           xi_ref
           (upRen_tm_ty (upRen_tm_ty xi_ty))
           (upRen_tm_tm (upRen_tm_tm xi_tm)) s0)
  | .tlam s0 =>
      .tlam
        (ren_tm (upRen_ty_label xi_label) xi_ref
           (upRen_ty_ty xi_ty)
           (upRen_ty_tm xi_tm) s0)
  | .rlam s0 =>
    .rlam
        (ren_tm xi_label (up_ren xi_ref) xi_ty xi_tm s0)
  | .letr e1 e2 =>
    .letr (ren_tm xi_label xi_ref xi_ty xi_tm e1)
          (ren_tm xi_label (up_ren xi_ref) xi_ty (upRen_tm_tm xi_tm) e2)
  | .l_lam s0 =>
      .l_lam
        (ren_tm (upRen_label_label xi_label) xi_ref
           (upRen_label_ty xi_ty)
           (upRen_label_tm xi_tm) s0)
  | .Op s0 s1 s2 =>
      .Op s0 (ren_tm xi_label xi_ref xi_ty xi_tm s1)
        (ren_tm xi_label xi_ref xi_ty xi_tm s2)
  | .zero s0 => .zero (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .app s0 s1 =>
     .app (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm xi_label xi_ref xi_ty xi_tm s1)
  | .alloc s0 =>
      .alloc (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .dealloc s0 =>
      .dealloc (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .assign s0 s1 =>
      .assign (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm xi_label xi_ref xi_ty xi_tm s1)
  | .tm_pair s0 s1 =>
      .tm_pair (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm xi_label xi_ref xi_ty xi_tm s1)
  | .left_tm s0 =>
      .left_tm (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .right_tm s0 =>
      .right_tm (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .inl s0 => .inl (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .inr s0 => .inr (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .case s0 s1 s2 =>
      .case (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm (upRen_tm_label xi_label) xi_ref (upRen_tm_ty xi_ty)
           (upRen_tm_tm xi_tm) s1)
        (ren_tm (upRen_tm_label xi_label) xi_ref (upRen_tm_ty xi_ty)
           (upRen_tm_tm xi_tm) s2)
  | .tapp s0 s1 =>
      .tapp (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_ty xi_label xi_ref xi_ty s1)
  | .lapp s0 s1 =>
      .lapp (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_label xi_label s1)
  | .rapp e0 re =>
    .rapp (ren_tm xi_label xi_ref xi_ty xi_tm e0)
          (ren_rexp xi_ref re)
  | .pack s s0 => .pack (ren_ty xi_label xi_ref xi_ty s) (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .rpack re t0 => .rpack (ren_rexp xi_ref re) (ren_tm xi_label xi_ref xi_ty xi_tm t0)
  | .unpack s0 s1 =>
      .unpack (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm (upRen_tm_label xi_label) xi_ref (upRen_tm_ty (upRen_ty_ty xi_ty))
           (upRen_tm_tm xi_tm) s1)
  | .if_tm s0 s1 s2 =>
      .if_tm (ren_tm xi_label xi_ref xi_ty xi_tm s0)
        (ren_tm xi_label xi_ref xi_ty xi_tm s1) (ren_tm xi_label xi_ref xi_ty xi_tm s2)
  | .if_c s0 s1 s2 =>
      .if_c (ren_label xi_label s0)
        (ren_tm xi_label xi_ref xi_ty xi_tm s1) (ren_tm xi_label xi_ref xi_ty xi_tm s2)
  | .sync s0 => .sync (ren_tm xi_label xi_ref xi_ty xi_tm s0)
  | .corr_case lab e => .corr_case (ren_label xi_label lab) (ren_tm xi_label xi_ref xi_ty xi_tm e)
  | .annot e t => .annot (ren_tm xi_label xi_ref xi_ty xi_tm e) (ren_ty xi_label xi_ref xi_ty t)
  | .default => .default
end

@[simp]
def subst_label
(sigma_label : Fin m_label -> label n_label) (s : label m_label) :
label n_label :=
  match s with
  | .var_label _ s0 => sigma_label s0
  | .latl s0 => .latl s0
  | .ljoin s0 s1 =>
      .ljoin (subst_label sigma_label s0) (subst_label sigma_label s1)
  | .lmeet s0 s1 =>
      .lmeet (subst_label sigma_label s0) (subst_label sigma_label s1)
  | .default => .default

@[simp]
def subst_corruption
(sigma_label : Fin m_label -> label n_label) (s : corruption m_label) :
corruption n_label :=
  match s with
  | .corr l1 => .corr (subst_label sigma_label l1)
  | .not_corr l1 => .not_corr (subst_label sigma_label l1)

@[simp]
def subst_constr
  (sigma_label : Fin m_label -> label n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | .condition s0 s1 s2 =>
      .condition s0 (subst_label sigma_label s1)
        (subst_label sigma_label s2)

@[simp]
def up_ty_label (sigma : Fin m -> label n_label)
  : Fin m -> label n_label :=
    (funcomp (ren_label id) sigma)

@[simp]
def up_ty_ty
  (sigma : Fin m -> ty n_label n_ref n_ty ) : Fin (m + 1) -> ty n_label n_ref (n_ty + 1) :=
    (cons (.var_ty var_zero)
         (funcomp (ren_ty id id shift ) sigma))

@[simp]
def up_label_label
  (sigma : Fin m -> label n_label) : Fin (m + 1) -> label (n_label + 1) :=
    (cons (.var_label "_" var_zero)
         (funcomp (ren_label shift) sigma))

@[simp]
def up_label_ty
  (sigma : Fin m -> ty n_label n_ty n_ref) : Fin m -> ty (n_label + 1) n_ty n_ref :=
    (funcomp (ren_ty shift id id) sigma)

@[simp]
def up_tm_label
  (sigma : Fin m -> label n_label)
  : Fin m -> label n_label :=
  (funcomp (ren_label id) sigma)

@[simp]
def up_tm_ty
  (sigma : Fin m -> ty n_label n_ref n_ty ) : Fin m -> ty n_label n_ref n_ty :=
  (funcomp (ren_ty id id id) sigma)

@[simp]
def up_tm_tm
  (sigma : Fin m -> tm n_label n_ref n_ty n_tm ) :
  Fin (m + 1) -> tm n_label n_ref n_ty (n_tm + 1) :=
  (cons (tm.mkD (.var_tm var_zero))
    (funcomp (ren_tm id id id shift ) sigma))

@[simp]
def up_rexp_tm_tm
  (sigma : Fin m -> tm n_label n_ref n_ty n_tm) :
  Fin (m + 1) -> tm n_label (n_ref + 1) n_ty (n_tm + 1) :=
  cons (.mkD (.var_tm var_zero))
    (funcomp (ren_tm id shift id shift) sigma)

@[simp]
def up_ty_tm
  (sigma : Fin m -> tm n_label n_ref n_ty n_tm ) : Fin m -> tm n_label n_ref (n_ty + 1) n_tm :=
  (funcomp (ren_tm id id shift id) sigma)

@[simp]
def up_rexp_ty
  (sigma : Fin m -> ty n_label n_ref n_ty ) : Fin m -> ty n_label (n_ref + 1) n_ty :=
  funcomp (ren_ty id shift id) sigma

@[simp]
def up_rexp (sigma : Fin m -> rexp n) : Fin (m + 1) -> rexp (n + 1) :=
  cons (.var (var_zero)) (funcomp (ren_rexp shift) sigma)

@[simp]
def up_label_tm
  (sigma : Fin m -> tm n_label n_ty n_tm n_ref) : Fin m -> tm (n_label + 1) n_ty n_tm n_ref :=
  (funcomp (ren_tm shift id id id) sigma)


def subst_rexp (sigma_ref : Fin m_ref -> rexp n_ref)
  (r : rexp m_ref) : rexp n_ref :=
  match r with
  | .var j => sigma_ref j
  | .op s r1 r2 => .op s (subst_rexp sigma_ref r1) (subst_rexp sigma_ref r2)
  | .const b => .const b


def subst_prop (sigma_ref : Fin m_ref -> rexp n_ref)
  (p : prop m_ref) : prop n_ref :=
    match p with
    | .peq re1 re2 => .peq (subst_rexp sigma_ref re1) (subst_rexp sigma_ref re2)
    | .pand p1 p2 => .pand (subst_prop sigma_ref p1) (subst_prop sigma_ref p2)
    | .por p1 p2 => .por (subst_prop sigma_ref p1) (subst_prop sigma_ref p2)
    | .pimpl p1 p2 => .pimpl (subst_prop sigma_ref p1) (subst_prop sigma_ref p2)
    | .pnot p1 => .pnot (subst_prop sigma_ref p1)
    | .pall p => .pall (subst_prop (up_rexp sigma_ref) p)


@[simp]
def subst_ty
(sigma_label : Fin m_label -> label n_label)
(sigma_ref : Fin m_ref -> rexp n_ref)
(sigma_ty : Fin m_ty -> ty n_label n_ref n_ty )
(s : ty m_label m_ref m_ty ) :
ty n_label n_ref n_ty :=
  match s with
  | .var_ty s0 => sigma_ty s0
  | .Any => .Any
  | .Unit => .Unit
  | .RData s0 re => .RData (subst_label sigma_label s0) (subst_rexp sigma_ref re)
  | .Data s0 => .Data (subst_label sigma_label s0)
  | .Ref s0 => .Ref (subst_ty sigma_label sigma_ref sigma_ty s0)
  | .refined t p =>
    .refined (subst_ty sigma_label sigma_ref sigma_ty t) (subst_prop sigma_ref p)
  | .arr s0 s1 =>
      .arr (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1)
  | .prod s0 s1 =>
      .prod (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1)
  | .sum s0 s1 =>
      .sum (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1)
  | .all s0 s1 =>
      .all (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) sigma_ref (up_ty_ty sigma_ty) s1)
  | .ex s0 s1 =>
      .ex (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) sigma_ref (up_ty_ty sigma_ty) s1)
  | .ex_r t0 =>
      .ex_r (subst_ty sigma_label (up_rexp sigma_ref) (up_rexp_ty sigma_ty) t0)
  | .all_r t0 =>
      .all_r (subst_ty sigma_label (up_rexp sigma_ref) (up_rexp_ty sigma_ty) t0)
  | .all_l s0 s1 s2 =>
      .all_l s0 (subst_label sigma_label s1)
        (subst_ty (up_label_label sigma_label) sigma_ref (up_label_ty sigma_ty) s2)
  | .t_if s0 s1 s2 =>
      .t_if (subst_label sigma_label s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1) (subst_ty sigma_label sigma_ref sigma_ty s2)
  | .Public => .Public
  | .default => .default

mutual

  @[simp]
  def subst_tm
  (sigma_label : Fin m_label -> label n_label)
  (sigma_ref : Fin m_ref -> rexp n_ref)
  (sigma_ty : Fin m_ty -> ty n_label n_ref n_ty )
  (sigma_tm : Fin m_tm -> tm n_label n_ref n_ty n_tm ) (s : tm m_label m_ref m_ty m_tm )
  : tm n_label n_ref n_ty n_tm :=
    match s with
    | .mk stx v => .mk stx (subst_tmX sigma_label sigma_ref sigma_ty sigma_tm v)

@[simp]
def subst_tmX
(sigma_label : Fin m_label -> label n_label)
(sigma_ref : Fin m_ref -> rexp n_ref)
(sigma_ty : Fin m_ty -> ty n_label n_ref n_ty )
(sigma_tm : Fin m_tm -> tm n_label n_ref n_ty n_tm ) (s : tmX m_label m_ref m_ty m_tm )
: tmX n_label n_ref n_ty n_tm :=
  match s with
  | .var_tm s0 => (sigma_tm s0).get
  | .error => .error
  | .skip => .skip
  | .bitstring s0 => .bitstring s0
  | .loc s0 => .loc s0
  | .fixlam nm s0 =>
      .fixlam nm
        (subst_tm (up_tm_label (up_tm_label sigma_label)) sigma_ref
           (up_tm_ty (up_tm_ty sigma_ty)) (up_tm_tm (up_tm_tm sigma_tm)) s0)
  | .tlam s0 =>
      .tlam
        (subst_tm (up_ty_label sigma_label) sigma_ref (up_ty_ty sigma_ty)
           (up_ty_tm sigma_tm) s0)
  | .rlam s0 =>
      .rlam
        (subst_tm sigma_label
            (cons (.var var_zero)
              (funcomp (ren_rexp shift) sigma_ref))
            (funcomp (ren_ty id shift id) sigma_ty)
            (funcomp (ren_tm id shift id id) sigma_tm) s0)
  | .letr e1 e2 =>
    .letr (subst_tm sigma_label sigma_ref sigma_ty sigma_tm e1)
          (subst_tm sigma_label
             (up_rexp sigma_ref)
             (funcomp (ren_ty id shift id) sigma_ty)
             (up_rexp_tm_tm sigma_tm)
             e2)
  | .l_lam s0 =>
      .l_lam
        (subst_tm (up_label_label sigma_label) sigma_ref  (up_label_ty sigma_ty)
           (up_label_tm sigma_tm) s0)
  | .Op s0 s1 s2 =>
      .Op s0 (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s2)
  | .zero s0 =>
      .zero (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .app s0 s1 =>
      .app (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
  | .alloc s0 =>
      .alloc (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .dealloc s0 =>
      .dealloc (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .assign s0 s1 =>
      .assign (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
  | .tm_pair s0 s1 =>
      .tm_pair (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
  | .left_tm s0 =>
      .left_tm (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .right_tm s0 =>
      .right_tm (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .inl s0 =>
      .inl (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .inr s0 =>
      .inr (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .case s0 s1 s2 =>
      .case (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm (up_tm_label sigma_label) sigma_ref (up_tm_ty sigma_ty)
           (up_tm_tm sigma_tm) s1)
        (subst_tm (up_tm_label sigma_label) sigma_ref (up_tm_ty sigma_ty)
           (up_tm_tm sigma_tm) s2)
  | .tapp s0 s1 =>
      .tapp (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1)
  | .lapp s0 s1 =>
      .lapp (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_label sigma_label s1)
  | .rapp s0 s1 =>
      .rapp (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_rexp sigma_ref s1)
  | .pack s0 s1 =>
      .pack (subst_ty sigma_label sigma_ref sigma_ty s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
  | .rpack re s1 =>
    .rpack (subst_rexp sigma_ref re)
           (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
  | .unpack s0 s1 =>
      .unpack (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm (up_tm_label (up_ty_label sigma_label)) sigma_ref
           (up_tm_ty (up_ty_ty sigma_ty)) (up_tm_tm (up_ty_tm sigma_tm)) s1)
  | .if_tm s0 s1 s2 =>
      .if_tm (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s2)
  | .if_c s0 s1 s2 =>
      .if_c (subst_label sigma_label s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s1)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s2)
  | .sync s0 =>
      .sync (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
  | .corr_case s0 s =>
      .corr_case (subst_label sigma_label s0)
        (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s)
  | .annot s0 s1 =>
      .annot (subst_tm sigma_label sigma_ref sigma_ty sigma_tm s0)
        (subst_ty sigma_label sigma_ref sigma_ty s1)
  | .default => .default
end

def shift_bound_by (shift_num : Nat) : Fin n -> Fin (n + shift_num) :=
  fun x => (x.addNat shift_num)

end Owl
