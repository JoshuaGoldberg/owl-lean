import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta

syntax "tc" : tactic

macro_rules
  | `(tactic| tc) =>
  `(tactic|
    first
    | apply has_type.T_Var
    | apply has_type.T_IUnit
    | apply has_type.T_Const
    | (apply has_type.T_Op; tc; tc)
    | (apply has_type.T_Zero; tc)
  )

def tm1 :=
  Owl {
    *
  }

def ty1 :=
  OwlTy {
    Unit
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
