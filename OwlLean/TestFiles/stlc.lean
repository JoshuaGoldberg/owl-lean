-- {p} + {~ p}


inductive Ty where
  | bool
  | arr : Ty -> Ty -> Ty


inductive Tm : Nat -> Type where
  | var : Fin n -> Tm n
  | abs : Tm (n + 1) -> Tm n
  | app : Tm n -> Tm n -> Tm n
  | true : Tm n
  | false : Tm n
  | ite : Tm n -> Tm n -> Tm n -> Tm n

abbrev Renaming n m := Fin n -> Fin m

@[simp]
def Renaming.comp (s : Fin n -> Fin m) (t : Fin m -> Fin k) :=
  fun x => t (s x)


def Cons (x : α) (s : Fin n -> α) : Fin (n + 1) -> α :=
    Fin.cases x s

@[simp]
def Tm.rename (t : Tm n) (s : Fin n -> Fin m) : Tm m :=
  match t with
  | .var j => .var (s j)
  | .abs f => .abs (f.rename (Cons 0 (Renaming.comp s Fin.succ)))
  | .app a b => .app (a.rename s) (b.rename s)
  | .true => .true
  | .false => .false
  | .ite a b c => .ite (a.rename s) (b.rename s) (c.rename s)

abbrev Subst n m := Fin n -> Tm m

@[simp]
def Tm.subst (t : Tm n) (s : Fin n -> Tm m) : Tm m :=
  match t with
  | .var j => s j
  | .app a b => .app (a.subst s) (b.subst s)
  | .abs f => .abs (f.subst (Cons (.var 0) (fun x => (s x).rename Fin.succ)))
  | .true => .true
  | .false => .false
  | .ite a b c => .ite (a.subst s) (b.subst s) (c.subst s)


theorem Tm.rename_rename (e : Tm n) (s : Fin n -> Fin m) (t : Fin m -> Fin k) :
  (e.rename s).rename t =
  e.rename (Renaming.comp s t) := by
    induction e generalizing m k t <;> simp
    {
      rename_i ih
      rw [ih]
      congr
      unfold Renaming.comp
      unfold Cons
      funext x; cases x using Fin.cases
      simp
      simp
    }
    {
      grind
    }
    {
      rename_i ih1 ih2 ih3
      simp [ih1, ih2, ih3]
    }

theorem Tm.subst_rename (e : Tm n) (s : Fin n -> Tm m) (t : Fin m -> Fin k) :
  (e.subst s).rename t =
  e.subst (fun x => (s x).rename t) := by
    induction e generalizing m k t <;> simp
    {
      rename_i ih
      rw [ih]
      congr; funext x; cases x using Fin.cases <;> simp [Cons]
      rw [Tm.rename_rename]
      rw [Tm.rename_rename]
      congr
    }
    {
      rename_i ih1 ih2
      rw [ih1]
      constructor
      rfl
      grind
    }
    {
      rename_i ih1 ih2 ih3
      simp [ih1, ih2, ih3]
    }

theorem Tm.rename_subst (e : Tm n) (s : Fin n -> Fin m) (t : Fin m -> Tm k) :
  (e.rename s).subst t =
  e.subst (fun x => t (s x)) := by
    induction e generalizing m k t <;> simp
    {
      rename_i ih
      rw [ih]
      simp [Cons]
      congr
      funext x; cases x using Fin.cases <;> simp [Cons]
    }
    {
      rename_i ih1 ih2
      simp [ih1, ih2]
    }
    {
      rename_i ih1 ih2 ih3
      simp [ih1, ih2, ih3]
    }

theorem Tm.subst_id (e : Tm n) :
  e.subst (fun x => .var x) = e := by
    induction e
    · simp
    {
      rename_i ih
      simp

      conv =>

        rhs
        rw [<- ih]
        rfl
      congr
      funext x
      unfold Cons
      cases x using Fin.cases <;> simp
    }
    rename_i ih1 ih2; simp [ih1, ih2]
    simp
    simp
    simp
    rename_i ih1 ih2 ih3
    simp [ih1, ih2, ih3]

theorem Tm.subst0 (e : Tm 0) (s : Fin 0 -> Tm 0) :
  e.subst s = e := by
    conv =>
      rhs
      rw [<- (Tm.subst_id e)]
      rfl
    congr
    funext x
    cases x; omega




theorem Tm.subst_subst (e : Tm n) (s : Fin n -> Tm m) (t : Fin m -> Tm k) :
  (e.subst s).subst t =
  e.subst (fun x => (s x).subst t) := by
    induction e generalizing m k t <;> simp
    {
      rename_i ih
      rw [ih]
      congr; funext x; cases x using Fin.cases <;> simp [Cons]
      rw [Tm.subst_rename]
      rw [Tm.rename_subst]
      congr
    }
    {
      rename_i ih1 ih2
      simp [ih1, ih2]
    }
    {
      rename_i ih1 ih2 ih3
      simp [ih1, ih2, ih3]
    }



inductive Tm.eval : Tm 0 -> Tm 0 -> Prop
  | eval_true : Tm.eval .true .true
  | eval_false : Tm.eval .false .false
  | eval_abs : Tm.eval (.abs k) (.abs k)
  | eval_app :
    Tm.eval e1 (.abs f) ->
    Tm.eval e2 v ->
    Tm.eval (f.subst (fun _ => v)) res ->
    Tm.eval (.app e1 e2) res
  | eval_ite_true :
    Tm.eval b .true ->
    Tm.eval e1 res ->
    Tm.eval (.ite b e1 e2) res
  | eval_ite_false :
    Tm.eval b .false ->
    Tm.eval e2 res ->
    Tm.eval (.ite b e1 e2) res

def Subst.wf (s : Fin n -> Tm 0) :=
  ∀ x, (s x).eval (s x)

def Ctx n := Fin n -> Ty

inductive Tm.has_type : Tm n -> Ctx n -> Ty -> Prop
  | var_t (x : Fin n) : Tm.has_type (.var x) g (g x)
  | app_t : Tm.has_type e1 g (.arr t1 t2) -> Tm.has_type e2 g t1 -> Tm.has_type (.app e1 e2) g t2
  | abs_t (k : Tm _): Tm.has_type k (Cons t g) s -> Tm.has_type (.abs k) g (.arr t s)
  | true_t : Tm.has_type .true g .bool
  | false_t : Tm.has_type .false g .bool
  | ite_t :
    Tm.has_type b g .bool ->
    Tm.has_type e1 g t ->
    Tm.has_type e2 g t ->
    Tm.has_type (.ite b e1 e2) g t



@[simp]
def Ty.vrel (t : Ty) (e: Tm 0) :=
  match t with
  | .bool => (e = Tm.true) ∨ (e = Tm.false)
  | .arr t1 t2 =>
    ∃ f, (e = Tm.abs f) ∧
    ∀ v,
      t1.vrel v ->
      ∃ res, t2.vrel res ∧
        (Tm.app (.abs f) v).eval res


theorem Ty.vrel_eval_det (t : Ty) (v : Tm 0) :
  t.vrel v ->
  v.eval v2 ->
  v = v2 := by
    intro h hv
    induction t
    simp at h
    cases h <;> subst_eqs
    cases hv; rfl
    cases hv; rfl
    simp at h
    obtain ⟨f, hf1, hf2⟩ := h
    subst_eqs
    cases hv; rfl

@[simp]
theorem Ty.vrel_eval_same (t : Ty) (v : Tm 0) :
  t.vrel v ->
  v.eval v := by
    intro h
    induction t
    simp at h
    cases h <;> subst_eqs <;> constructor
    simp at h
    obtain ⟨f, hf1, hf2⟩ := h
    subst_eqs
    constructor






def Ty.erel (t : Ty) (e : Tm 0) :=
  ∃ res,
    t.vrel res ∧ e.eval res

def Ctx.rel (c : Ctx n) (g : Fin n -> Tm 0) :=
  forall x,
    (c x).vrel (g x)


theorem fundamental_theorem (e : Tm n) :
  e.has_type g t ->
  ∀ s,
    Subst.wf s ->
    g.rel s ->
    t.erel (e.subst s) := by
    intro h
    intros s Hs Hs'
    induction h with
    | var_t x =>
      exists (s x)
      constructor
      apply Hs'
      apply Hs
    | app_t h1 h2 ih1 ih2 =>  {
      specialize (ih1 s Hs Hs')
      specialize (ih2 s Hs Hs')
      obtain ⟨v1, ⟨f, hf1, hf2⟩, h1₂⟩  := ih1
      obtain ⟨v2, h2₁, h2₂⟩  := ih2
      specialize (hf2 v2 (by grind))
      obtain ⟨res, hres⟩ := hf2
      exists res
      constructor; grind
      simp [Tm.subst]
      constructor
      subst hf1
      apply h1₂
      apply h2₂
      obtain ⟨hres1, hres2⟩ := hres
      cases hres2 with
      | eval_app hf hv2 =>
        rename_i v _
        have: v2 = v := by
          apply Ty.vrel_eval_det
          apply h2₁
          assumption
        subst this
        cases hf
        assumption
    }
    | abs_t k h ih => {
      simp [Ty.erel]
      exists (k.abs.subst s)
      constructor
      simp [Tm.subst]
      intros v Hv

      specialize (ih (Cons v s) _ _)
      {
        intros x
        cases x using Fin.cases
        {
          simp [Cons]
          apply Ty.vrel_eval_same
          apply Hv
        }
        {
          simp [Cons]
          apply Hs
        }
      }
      {
        intro x
        cases x using Fin.cases
        {
          simp [Cons]; assumption
        }
        {
          simp [Cons]
          apply Hs'
        }
      }
      obtain ⟨v, hv, hv'⟩ := ih
      exists v
      constructor
      assumption
      constructor
      constructor
      apply Ty.vrel_eval_same
      apply Hv
      rw [Tm.subst_subst]
      rename_i v'
      have:
        (k.subst fun x => (Cons (Tm.var 0) (fun x => (s x).rename Fin.succ) x).subst fun x => v')
        =
        (k.subst (Cons v' s))
        := by  {
          congr
          funext x
          cases x using Fin.cases <;> simp [Cons]
          rw [Tm.rename_subst]
          rw [Tm.subst0]
        }
      rw [this]; apply hv'
      constructor
    }
    | true_t => {
      exists Tm.true
      simp; constructor
    }
    | false_t => {
      exists Tm.false
      simp; constructor
    }
    | ite_t h1 h2 h3 ih1 ih2 ih3 => {
        specialize (ih1 s Hs Hs')
        specialize (ih2 s Hs Hs')
        specialize (ih3 s Hs Hs')
        obtain ⟨b, Hb⟩ := ih1
        obtain ⟨Hb1, Hb2⟩ := Hb


        simp [Ty.vrel] at Hb1
        cases Hb1
        {
          subst_eqs
          obtain ⟨res, Hres1, Hres2⟩ := ih2
          exists res
          constructor
          assumption
          apply Tm.eval.eval_ite_true
          assumption
          assumption
        }
        {

          subst_eqs

          obtain ⟨res, Hres1, Hres2⟩ := ih3
          exists res
          constructor
          assumption
          apply Tm.eval.eval_ite_false
          assumption
          assumption
        }
    }
