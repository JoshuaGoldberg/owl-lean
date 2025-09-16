import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta

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
  )
  | `(tactic| st) =>
  `(tactic|
    first
    | apply subtype.ST_Any
    | apply subtype.ST_Unit
  )

def tm_spec :=
  Owl {
    (Λ a . *) [[Unit]]
  }

def ty_spec :=
  OwlTy{
    Unit
  }

theorem tc_spec : has_type (@empty_phi 0) empty_delta empty_gamma tm_spec
  (Owl.subst_ty .var_label (Owl.cons Owl.ty.Unit .var_ty) Owl.ty.Unit) := by
  tc

-- TYPECHECKER TESTS
def tm1 :=
  Owl {
    zero (["11101"])
  }

noncomputable def ty1 :=
  OwlTy {
    (Data ⟨Owl.L.bot⟩)
  }

-- example : True has type bool
theorem tc1 : has_type (@empty_phi 0) empty_delta empty_gamma tm1 ty1 := by
  tc

-- test operator
def coin_flip : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def tm2 :=
  Owl {
    ⟨coin_flip⟩ (["1101"], ["1001"])
  }

noncomputable def ty2 :=
  OwlTy {
    (Data ⟨Owl.L.bot⟩)
  }

-- example : True has type bool
theorem tc2 : has_type (@empty_phi 0) empty_delta empty_gamma tm2 ty2 := by
  tc

def tm3 :=
  Owl {
    fix f (x) (zero x)
  }

noncomputable def ty3 :=
  OwlTy {
    ((Data ⟨Owl.L.bot⟩) -> (Data ⟨Owl.L.bot⟩))
  }

theorem tc3 : has_type (@empty_phi 0) empty_delta empty_gamma tm3 ty3 := by
  tc
