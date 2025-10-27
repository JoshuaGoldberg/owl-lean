-- IMPORT THIS FILE WHEN PERFORMING TYPECHECKER TESTS
-- INCLUDES ALL NECESSARY FUNCTIONAL FILES, PLUS NOTATION

import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTypecheck

open Lean PrettyPrinter Delaborator SubExpr

set_option pp.notation true
set_option pp.fullNames false
set_option pp.universes false
set_option pp.proofs false

set_option maxHeartbeats 1000000

notation:50 "<" Φ ", " Ψ " ⊨ " co ">" => phi_psi_entail_corr Φ Ψ co
notation h "::" t => pcons h t
notation "Ψ∅" => empty_phi 0
notation "Φ∅" => empty_psi 0
notation "Ψ∅" => empty_phi
notation "Φ∅" => empty_psi
notation "Δ∅" => empty_delta
notation "Γ∅" => empty_gamma
notation "corr(" l ")"  => Owl.corruption.corr l
notation "¬corr(" l ")" => Owl.corruption.not_corr l
notation pm " ▷ " ψ => subst_psi_context pm ψ
notation "⟪" l "⟫" => Owl.label.latl l
notation "⊑" => Owl.cond_sym.leq
notation "⊒" => Owl.cond_sym.geq
notation "⊏" => Owl.cond_sym.lt
notation "⊐" => Owl.cond_sym.gt
notation "ℓ" n => Owl.label.var_label n
notation "(" a c b ")" => Owl.constr.condition c a b
notation "↑" a => lift_phi a
notation "↑" a => lift_psi a
notation "[" a "]" => Owl.ren_label id a
notation h "::" t => Owl.cons h t
notation "⊥" => Owl.L.bot

@[delab Owl.cond_sym.leq]
def delabLeq : Delab := do
  `("⊑")

@[app_unexpander Owl.Lattice.bot]
def unexpOwlBot : Unexpander
| `($_ $_) => `(⊥)
| _        => throw ()
