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

syntax "check" : tactic
syntax "synth" : tactic

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
  | `(tactic| check) => `(tactic|
    first
    | (apply check.C_Lam; check)
    | (apply check.C_Inl; check)
    | (apply check.C_Inr; check)
    | (apply check.C_Pack; check; st)
    | (apply check.C_TLam; check)
    | (apply check.C_LLam; check)
    | (apply check.C_Sub; synth; st)
  )
  | `(tactic| synth) => `(tactic|
    first
    | (apply synth.S_Var)
    | (apply synth.S_Unit)
    | (apply synth.S_Const)
    | (apply synth.S_App; synth; check)
    | (apply synth.S_Deref; synth)
    | (apply synth.S_ProjL; synth)
    | (apply synth.S_ProjR; synth)
    | (apply synth.S_Case; synth; check; check)
    | (apply synth.S_TApp; synth; st)
    | (apply synth.S_LApp; synth; pec)
    | (apply synth.S_LApp; synth; pec)
    | (apply synth.S_Unpack; synth; check)
    | (apply synth.S_Op; check; check)
    | (apply synth.S_Zero; synth)
    | (apply synth.S_If; check; check; check)
    | (apply synth.S_Assign; synth; check)
    | (apply synth.S_Pair; synth; synth)
    | (apply synth.S_IfC; synth; synth; synth)
    | (apply synth.S_Alloc; synth)
    | (apply synth.S_Sync; synth)
    | (apply synth.S_Annot; check)
  )

-- NEW Tests!!!

theorem test_unit : check empty_phi empty_delta empty_gamma (Owl { * }) (OwlTy { Unit }) := by check

theorem test_const : check empty_phi empty_delta empty_gamma
  (Owl { ["101"] }) (OwlTy { Data ⟨Owl.sec⟩ }) := by check

theorem test_pair : check empty_phi empty_delta empty_gamma
  (Owl { ⟨*, *⟩ }) (OwlTy { Unit * Unit }) := by check

theorem test_proj :
  check empty_phi empty_delta empty_gamma
    (Owl { π1 ⟨*, ["1"]⟩ }) (OwlTy { Unit }) := by check

-- Function application
theorem test_lambda : check empty_phi empty_delta empty_gamma
  (Owl { fix f(x) * }) (OwlTy { Unit -> Unit }) := by check

-- Sum types
theorem test_inl : check empty_phi empty_delta empty_gamma
  (Owl { ı1 * }) (OwlTy { Unit + (Data ⟨Owl.pub⟩) }) := by check
