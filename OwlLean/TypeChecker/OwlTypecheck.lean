import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta


@[simp] theorem interp_latl (x : Owl.L.labels) :
  interp_lattice (Owl.label.latl x) = x := rfl

@[simp] theorem subst_label_latl (pm : phi_map l) (x : Owl.L.labels) :
  Owl.subst_label pm (Owl.label.latl x) = Owl.label.latl x := by
  simp [Owl.subst_label]

-- Assume you have basic lattice lemmas
axiom L_bot_leq (x : Owl.L.labels) : Owl.L.leq Owl.L.bot x = true
axiom L_leq_refl (x : Owl.L.labels) : Owl.L.leq x x = true

-- Main tactic for phi_entails_c
syntax "pec" : tactic

syntax "tc" : tactic
syntax "st" : tactic

macro_rules
  | `(tactic| tc) =>
  `(tactic|
    first
    | apply has_type.T_Var
    | apply has_type.T_IUnit
    | apply has_type.T_Const
    | (apply has_type.T_Op; tc; tc)
    | (apply has_type.T_Zero; tc)
    | (apply has_type.T_If; tc; tc; tc)
    | (apply has_type.T_IRef; tc)
    | (apply has_type.T_ERef; tc)
    | (apply has_type.T_Assign; tc; tc)
    | (apply has_type.T_IFun; tc)
    | (apply has_type.T_EFun; tc; tc; tc)
    | (apply has_type.T_IProd; tc; tc)
    | (apply has_type.T_EProdL; tc)
    | (apply has_type.T_EProdR; tc)
    | (apply has_type.T_ISumL; tc)
    | (apply has_type.T_ISumR; tc)
    | (apply has_type.T_ESum; tc; tc; tc)
    | (apply has_type.T_IUniv; tc)
    | (apply has_type.T_EUniv; st; tc)
    | (apply has_type.T_IExist; tc; st)
    | (apply has_type.T_EExist; tc; tc)
    | (apply has_type.T_ILUniv; tc)
    | (apply has_type.T_ELUniv (cs := .geq) (lab := .latl L.bot); pec; tc)
    | (apply has_type.T_LIf; tc; tc)
    | (apply has_type.T_Sync; tc)
    | (apply has_type.T_Sub; st; tc)
  )
  | `(tactic| st) =>
  `(tactic|
    first
    | apply subtype.ST_Any
    | apply subtype.ST_Unit
    | (apply subtype.ST_Var; st)
    | (apply subtype.ST_Data; pec)
    | (apply subtype.ST_Func; st; st)
    | (apply subtype.ST_Prod; st; st)
    | (apply subtype.ST_Sum; st; st)
    | (apply subtype.ST_Ref)
    | (apply subtype.ST_Univ; st; st)
    | (apply subtype.ST_Exist; st; st)
    | (apply subtype.ST_LatUniv; pec; st)
    | (apply subtype.ST_IfElimL; pec; st)
    | (apply subtype.ST_IfElimR; pec; st)
    | (apply subtype.ST_IfElimL; pec; st)
    | (apply subtype.ST_IfIntroR; pec; st)
    | (apply subtype.ST_Lem; st; st)
  )
  | `(tactic| pec) => `(tactic|
    intro pm h_valid;
    unfold phi_map_holds valid_constraint;
    simp only [interp_lattice, Owl.subst_label];
    first
    | exact L_leq_refl _
    | exact L_bot_leq _
    | rfl
    | simp [Owl.L.leq]
  )

theorem test_empty_entails_bot_geq :
  (empty_phi : phi_context 1) |= (Owl.constr.condition .geq (Owl.label.latl Owl.L.bot) (Owl.label.latl Owl.L.bot)) := by
  pec

noncomputable def c : Owl.constr 0 := (Owl.constr.condition .leq (Owl.label.latl Owl.L.bot) (Owl.label.latl Owl.L.bot))

axiom top : Owl.Lcarrier
axiom middle : Owl.Lcarrier
axiom middle_leq_top : Owl.L.leq middle top = true

theorem test_context_self : [c, c, c, c, c] |= c := by
  pec

def tm1 := Owl { * }
def ty1 := OwlTy { Unit }

theorem test_unit :
  has_type empty_phi empty_delta empty_gamma tm1 ty1 := by tc

-- Bitstring test
def tm2 := Owl { ["101"] }
noncomputable def ty2 := OwlTy { Data ⟨Owl.L.bot⟩ }

theorem test_bitstring :
  has_type empty_phi empty_delta empty_gamma tm2 ty2 := by tc

-- Pair test
def tm3 := Owl { ⟨*, *⟩ }
def ty3 := OwlTy { Unit * Unit }

theorem test_pair :
  has_type empty_phi empty_delta empty_gamma tm3 ty3 := by tc

-- Function test (fixpoint)
def tm4 := Owl { fix f(x) x }
def ty4 := OwlTy { Unit -> Unit }

theorem test_fixlam :
  has_type empty_phi empty_delta empty_gamma tm4 ty4 := by tc

-- Type abstraction
def tm5 := Owl { Λ t . * }
def ty5 := OwlTy { ∀ t <: Any . Unit }

theorem test_type_abs :
  has_type empty_phi empty_delta empty_gamma tm5 ty5 := by tc

-- Label abstraction
def tm6 := Owl { Λβ l . * }
noncomputable def ty6 := OwlTy { ∀ l ⊒ ⟨Owl.L.bot⟩ . Unit }

theorem test_label_abs :
  has_type empty_phi empty_delta empty_gamma tm6 ty6 := by tc

-- Pack/existential
def tm7 := Owl { pack (Unit, *) }
def ty7 := OwlTy { ∃ t <: Any . t }

theorem test_pack :
  has_type empty_phi empty_delta empty_gamma tm7 ty7 :=
    by tc

-- If-then-else
def tm8 := Owl { if ["1"] then * else * }
def ty8 := OwlTy { Unit }

theorem test_if :
  has_type empty_phi empty_delta empty_gamma tm8 ty8 := by tc

-- Zero operation
def tm9 := Owl { zero ["101"] }
noncomputable def ty9 := OwlTy { Data ⟨Owl.L.bot⟩ }

theorem test_zero :
  has_type empty_phi empty_delta empty_gamma tm9 ty9 := by tc

-- Test subsumption: Data bot <: Any
def tm10 := Owl { * }
def ty10 := OwlTy { Unit }

theorem test_subsumption :
  has_type empty_phi empty_delta empty_gamma tm10 ty10 := by tc

-- Test subtyping directly
theorem test_subtype_data_any :
  subtype empty_phi empty_delta
    (OwlTy { Data ⟨Owl.L.bot⟩ })
    (OwlTy { Any }) := by st

theorem test_subtype_unit_unit :
  subtype empty_phi empty_delta
    (OwlTy { Unit })
    (OwlTy { Unit }) := by st

theorem test_entails_bot :
  (@empty_phi 0) |= (Owl.constr.condition .geq (Owl.label.latl Owl.L.bot) (Owl.label.latl Owl.L.bot)) := by
  pec

def tm_spec :=
  Owl {
    (Λ a . *) [[Unit]]
  }

def ty_spec :=
  OwlTy {
    Unit
  }

theorem tc_spec : has_type (@empty_phi 0) empty_delta empty_gamma tm_spec
  (Owl.subst_ty .var_label (Owl.cons Owl.ty.Unit .var_ty) Owl.ty.Unit) := by
  tc

def tm_spec2 :=
  Owl {
    (Λ a . *)
  }

axiom high : Owl.Lcarrier

noncomputable def ty_spec2 :=
  OwlTy{
    (∀ a <: (Data ⟨high⟩) . Unit)
  }

theorem tc_spec2 : has_type (@empty_phi 0) empty_delta empty_gamma tm_spec2 ty_spec2:= by
  tc

-- TYPECHECKER TESTS
def tm_1 :=
  Owl {
    zero (["11101"])
  }

noncomputable def ty_1 :=
  OwlTy {
    (Data ⟨Owl.L.bot⟩)
  }

-- example : True has type bool
theorem tc1 : has_type (@empty_phi 0) empty_delta empty_gamma tm_1 ty_1 := by
  tc

-- test operator
def coin_flip : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def tm_2 :=
  Owl {
    ⟨coin_flip⟩ (["1101"], ["1001"])
  }

noncomputable def ty_2 :=
  OwlTy {
    (Data ⟨Owl.L.bot⟩)
  }

-- example : True has type bool
theorem tc2 : has_type (@empty_phi 0) empty_delta empty_gamma tm_2 ty_2 := by
  tc

def tm_3 :=
  Owl {
    fix f (x) (zero x)
  }

noncomputable def ty_3 :=
  OwlTy {
    ((Data ⟨Owl.L.bot⟩) -> (Data ⟨Owl.L.bot⟩))
  }

theorem tc3 : has_type (@empty_phi 0) empty_delta empty_gamma tm_3 ty_3 := by
  tc
