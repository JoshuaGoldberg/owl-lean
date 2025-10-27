import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping
open Lean PrettyPrinter Delaborator SubExpr

set_option maxHeartbeats 1000000

set_option pp.notation true
set_option pp.fullNames false
set_option pp.universes false
set_option pp.proofs false

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

def genKey : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def enc : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def dec : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def rand : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def eq : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def ENC :=
  OwlTy [lK, lM] [tau] {
    (∃ alphaK <: (Data lK) .
                  (alphaK *
                   ((corr (lK) ? ((Public * Public) -> Public) : ((alphaK * tau) -> Public)) *
                    (corr (lK) ? ((Public * Public) -> Public) : ((alphaK * Public) -> (tau + Unit))))))
  }

def EncIdeal :=
  Owl [lK, lM] [tau] [] {
    let k = (⟨genKey⟩ (["0"], ["0"]) : Data lK) in
    let L = alloc (λ (null : Public) : (tau + Unit) => ı2 *) in
    let enc' = (if corr (lK) then
                  (λ (x : Public * Public) : Public => ⟨enc⟩ (π1 x, π2 x))
                else
                  λ (x : (Data lK * tau)) : Public =>
                    let c = ⟨rand⟩ (zero ((π2 x) : Data lM), ["0"]) in
                    let L_old = (! L) in
                    let u = L := (λ (y : Public) : (tau + Unit) =>
                        if ⟨eq⟩(y, c) then ı1 (π2 x) else L_old [y])
                    in
                    c)
    in
    let dec' = (if corr (lK) then
                  λ (x : Public * Public) : Public => ⟨dec⟩ (π1 x, π2 x)
                else
                  λ (x : (Data lK * Public)) : (tau + Unit) => (!L) [π2 x])
    in
    pack (Data lK, ⟨k, ⟨(enc'), (dec')⟩⟩)
  }

theorem EncIdeal.wf :
  ( ( lK, lM ⊏ lK );
  · ;
  ( tau <: Data lM );
  · ;
   ($ EncIdeal [lK, lM] [tau] []) ⊢ ($ ENC [lK, lM] [tau])) := by
    tc_man (
      try simp
      try auto_solve_fast

    )
