import Lean


namespace Vec

inductive vec (α : Type u) : Nat → Type u
| nil  : vec α 0
| cons : α → vec α n → vec α (n + 1)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

def vec.map (xs : vec a n) (f : Fin n -> a -> b) : vec b n :=
  match xs with
  | nil => nil
  | cons x ys => cons (f 0 x) (ys.map (fun i x => f (Fin.succ i) x))

def vec.get (v : vec a n) (i : Fin n) : a :=
  match v with
  | nil => nomatch i
  | cons x xs => Fin.cases x xs.get i

def vec.set (v : vec a n) (i : Fin n) (x : a)  : vec a n :=
  match v with
  | nil => nomatch i
  | cons y ys => Fin.cases (cons x ys) (fun i => cons y (ys.set i x)) i

def vec.toList (v : vec a n) : List a :=
  match v with
  | nil => []
  | cons x xs => x :: xs.toList

@[simp]
def vec.init (x : α) : vec α n :=
  match n with
  | 0 => nil
  | _ + 1 => cons x (init x)

@[simp]
def vec.restrict (v : vec a N) (M : Nat) (h : M ≤ N) : vec a M :=
  match M with
  | 0 => nil
  | M' + 1 =>
    match v with
    | nil => nomatch h
    | cons x xs => cons x (restrict xs M' (by omega))

@[simp]
theorem vec.get_set (v : vec a n) (i : Fin n) (x : a) :
  (v.set i x).get i = x := by
    induction v with
    | nil => nomatch i
    | cons y ys ih =>
      cases i using Fin.cases
      simp [set, get]
      simp [set, get]
      apply ih

@[simp]
theorem vec.get_init (x : a) (i : Fin n) :
  (vec.init x).get i = x := by
    induction n with
    | zero => nomatch i
    | succ n ih =>
      cases i using Fin.cases
      simp [init, get]
      apply ih

@[simp]
theorem vec.get_set_ne (v : vec a n) (i j : Fin n) (x : a) (h : ¬ i = j) :
  (v.set i x).get j = v.get j := by
    induction v with
    | nil => nomatch j
    | cons y ys ih =>
      simp [get, set]
      cases i using Fin.cases <;> cases j using Fin.cases
      grind
      simp [get]
      simp [get]
      simp [get]
      apply ih
      grind

@[simp]
theorem vec.restrict_restrict (v : vec a N) (M : Nat) (h : M ≤ N) (M' : Nat) (h' : M' ≤ M) h'' :
  (v.restrict M h).restrict M' h' = v.restrict M' h'' := by
    induction v generalizing M M' h'
    cases M <;> cases M' <;> simp [restrict]
    grind
    cases M <;> cases M' <;> simp [restrict]
    grind
    grind


@[simp]
theorem vec.restrict_get (v : vec a N) (M : Nat) (h : M ≤ N) (x : Fin M) :
  (v.restrict M h).get x = v.get (Fin.castLE h x) := by
    induction v generalizing M
    cases M <;> simp [restrict]
    grind
    cases M <;> simp [restrict]
    cases x; grind
    simp [get]
    cases x using Fin.cases <;> simp
    grind

theorem vec.ext (v1 v2 : vec a n) (h : ∀ x : Fin n, v1.get x = v2.get x) : v1 = v2 := by
 induction v1 with
 | nil => cases v2 <;> simp
 | cons x xs ih =>
    cases v2 <;> simp
    constructor
    specialize h 0
    simp [get] at h; assumption
    apply ih
    intros x; specialize h (Fin.succ x)
    simp [get] at h; assumption


def vec.castLength (v : vec a N) (h : N = M) : vec a M :=
  match h with
  | rfl => v

def vec.castTy (v : vec a N) (h : a = b) : vec b N :=
  match h with
  | rfl => v

def vec.cast {v : vec a N} (h : N = M) {b : Type u} (h' : a = b) : vec b M :=
  match h with
  | rfl => v.castTy h'


@[simp]
def vec.All (v : vec a n) (p : Fin n -> a -> Prop) : Prop :=
  match v with
  | .nil => True
  | .cons x xs => p 0 x /\ xs.All (fun i x => p (Fin.succ i) x)

def vec.ofList (xs : List a) : vec a xs.length :=
  match xs with
  | [] => nil
  | x :: xs => cons x (ofList xs)

theorem vec.ofList_get (xs : List a) (i : Fin xs.length) :
  (vec.ofList xs).get i = xs.get i := by
    induction xs with
    | nil => simp [ofList, get]; nomatch i
    | cons x xs ih =>
      simp [ofList]
      cases i using Fin.cases
      simp [get]
      apply ih

def vec.snoc (v : vec a n) (x : a) : vec a (n + 1) :=
  match v with
  | nil => cons x nil
  | cons y ys => cons y (ys.snoc x)

def vec.reverse (v : vec a n) : vec a n :=
  match v with
  | nil => nil
  | cons x xs => xs.reverse.snoc x

end Vec


abbrev ScopeMap (N : Nat) := Vec.vec Nat N

abbrev ScopeMap.empty (N : Nat) : ScopeMap N :=
  Vec.vec.init 0

abbrev ScopeMap.get (m : ScopeMap N) (x : Fin N) : Nat :=
  Vec.vec.get m x



abbrev ScopeMap.bump (m : ScopeMap N) (x : Fin N) : ScopeMap N :=
  Vec.vec.set m x (m.get x + 1)

theorem ScopeMap.ext (m1 m2 : ScopeMap N) (h : ∀ x : Fin N, m1.get x = m2.get x) : m1 = m2 := by
  apply Vec.vec.ext
  assumption

abbrev ScopeMap.ofList (xs : List Nat) : ScopeMap xs.length :=
  Vec.vec.ofList xs

@[simp]
theorem ScopeMap.ofList_get (xs : List Nat) (i : Fin xs.length) :
  (ScopeMap.ofList xs).get i = xs.get i := by
    unfold ScopeMap.ofList
    simp [get]
    apply Vec.vec.ofList_get

theorem ScopeMap.get_bump_eq (m : ScopeMap N) (x : Fin N) :
  (m.bump x).get x = m.get x + 1 := by simp

theorem ScopeMap.get_bump_ne (m : ScopeMap N) (x y : Fin N) (h : ¬ x = y) :
  (m.bump x).get y = m.get y := by
    apply Vec.vec.get_set_ne
    assumption

@[simp]
theorem ScopeMap.get_bump (m : ScopeMap N) (x y : Fin N) :
  (m.bump x).get y = if x = y then m.get x + 1 else m.get y := by
    by_cases h : x = y
    subst h
    simp
    simp [h]



theorem ScopeMap.bump_bump {m : ScopeMap N} {x y : Fin N} :
  (m.bump x).bump y = (m.bump y).bump x := by
    apply ScopeMap.ext
    intros z
    simp
    grind

structure ScopeMap.renaming (m m' : ScopeMap N) where
  apply :
    (x : Fin N) -> Fin (m.get x) -> Fin (m'.get x)

abbrev ScopeMap.restrict (m : ScopeMap N) (M : Nat) (h : M ≤ N := by simp) :
  ScopeMap M :=
    Vec.vec.restrict m M h

@[simp]
theorem ScopeMap.restrict_get (m : ScopeMap N) (M : Nat) (h : M ≤ N) (x : Fin M) :
  (m.restrict M h).get x = m.get (Fin.castLE h x) := by
    unfold ScopeMap.restrict
    unfold ScopeMap.get
    rw [Vec.vec.restrict_get]


theorem ScopeMap.restrict_bump (m : ScopeMap N)  (M : Nat) (h : M ≤ N) (x : Fin M) :
  (m.restrict M h).bump x = (m.bump (x.castLE h)).restrict M h := by
    apply ScopeMap.ext
    intros y
    simp
    by_cases h : x = y
    subst h; simp
    simp [h]
    intros
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp at *
    grind


theorem ScopeMap.bump_restrict (m : ScopeMap N) (M : Nat) (h : M ≤ N) (x : Fin N) :
  (m.bump x).restrict M h = if h' : x < M then (m.restrict M h).bump (x.castLT h') else m.restrict M h := by
    by_cases h' : x < M
    simp [h']
    apply ScopeMap.ext; intros y
    simp
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp at *
    simp [h']
    apply ScopeMap.ext; rintro ⟨y, hy⟩
    cases x; simp; intro h; subst h
    grind

theorem ScopeMap.bump_restrict_ge (m : ScopeMap N) (M : Nat) (h : M ≤ N) (x : Fin N) :
  x >= M ->
  (m.bump x).restrict M h = m.restrict M h := by
    intro h
    rw [ScopeMap.bump_restrict]
    split
    grind
    simp


abbrev ScopeMap.renaming.id {m : ScopeMap xs} : m.renaming m :=
  ⟨fun _ n => n⟩

abbrev up_ren (xi : Fin m -> Fin n) : Fin (m + 1) -> Fin (n + 1) :=
  Fin.cases 0 (Fin.succ ∘ xi)


@[simp]
theorem ScopeMap.restrict_restrict (m : ScopeMap N) (M : Nat) (h : M ≤ N) (M' : Nat) (h' : M' ≤ M) h'' :
  (m.restrict M h).restrict M' h' = m.restrict M' h'' := by
    unfold ScopeMap.restrict
    rw [Vec.vec.restrict_restrict]


abbrev ScopeMap.renaming.bump {m : ScopeMap N} (r : m.renaming m') (x : Fin N) :
  (m.bump x).renaming (m'.bump x) :=
  ⟨ fun y n =>
     if h : x = y then
       by subst h; simp at n; simp
          exact Fin.cases 0 (Fin.succ ∘ (r.apply x)) n
      else by
        simp [ScopeMap.get]
        simp at n
        simp [h]
        simp [h] at n
        apply r.apply y n
    ⟩

abbrev ScopeMap.renaming.restrict {m : ScopeMap N} (r : m.renaming m') {M : Nat} (h : M ≤ N := by simp) :
  (m.restrict M h).renaming (m'.restrict M h) :=
  ⟨ fun x i =>
     by
      simp at i
      simp
      exact r.apply (Fin.castLE h x) i
  ⟩

abbrev ScopeMap.renaming.empty {m : ScopeMap N} : (ScopeMap.empty N).renaming m :=
 ⟨ fun x i => by
   simp at i
   nomatch i ⟩

abbrev ScopeMap.lift  {m : ScopeMap N} (n : Fin N)  : ScopeMap.renaming m (ScopeMap.bump m n) :=
  ⟨ fun x i =>
     if h : n = x then
      by subst h; simp; exact Fin.succ i
     else by
      rw [ScopeMap.get_bump_ne]
      apply i
      assumption
    ⟩



structure ScopeFunctor (N : Nat)  (x : Fin N)  where
  val : (m : ScopeMap N) -> Type
  rename : (m : ScopeMap N) -> (m' : ScopeMap N) -> (r : ScopeMap.renaming m m') -> val m -> val m'
  var : Fin (m.get x) -> val m


structure ScopeMap.Subst N
    (Val : (x : Fin N)  -> ScopeFunctor N x)
    (m m' : ScopeMap N) where
  apply :
    (x : Fin N) ->
    Fin (m.get x) -> (Val x).val m'

abbrev ScopeMap.Subst.bump {N} (x : Fin N)
  {Val : (x : Fin N)  -> ScopeFunctor N x}
  {m m' : ScopeMap N}
  (s : ScopeMap.Subst N Val m m') : ScopeMap.Subst N Val (m.bump x) (m'.bump x) :=
   ⟨ fun y i =>
       if heq : x = y then by
          subst heq
          simp at i
          refine (Fin.cases ((Val x).var (by simp; exact 0)) (fun i => (Val x).rename _ _ (ScopeMap.lift x) (s.apply x i)) i)
     else by
       rw [ScopeMap.get_bump_ne] at i
       apply (Val y).rename _ _ (ScopeMap.lift x) (s.apply y i)
       assumption
    ⟩

abbrev ScopeMap.Subst.down {N : Nat} {x : Fin N} {Val : (x : Fin N) -> ScopeFunctor N x} {m : ScopeMap N} (v : (Val x).val m) : ScopeMap.Subst N Val (m.bump x) m :=
  ⟨fun y i =>
    if heq : x = y then (by subst heq; simp at i; exact (Fin.cases v (Val x).var i) ) else
     by
       apply (Val y).var
       rw [ScopeMap.get_bump_ne] at i
       apply i
       assumption
  ⟩
