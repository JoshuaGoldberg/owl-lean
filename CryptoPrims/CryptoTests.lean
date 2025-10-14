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

notation:50 Φ ", " Ψ " ⊨ " co => phi_psi_entail_corr Φ Ψ co
notation h "::" t => pcons h t
notation "Φ∅" => empty_phi
notation "Ψ∅" => empty_psi
notation "corr(" l ")"  => Owl.corruption.corr l
notation "¬corr(" l ")" => Owl.corruption.not_corr l
notation pm " ▷ " ψ => subst_psi_context pm ψ
notation "⟪" l "⟫"   => Owl.label.latl l
notation "⊥"        => Owl.label.latl Owl.L.bot
notation "⊑" => Owl.cond_sym.leq
notation "⊒" => Owl.cond_sym.geq
notation "⊏" => Owl.cond_sym.lt
notation "⊐" => Owl.cond_sym.gt
notation "ℓ" n => Owl.label.var_label n
notation "(" a c b ")" => Owl.constr.condition c a b

-- non functional
def genKey : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def enc : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def rand : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)


theorem enc_ty :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ;
    Λ tau .
    let k = ⟨genKey⟩ (["000"], ["000"]) in
    let L = (alloc (λ null . ı2 *) : Ref (Public -> tau + Unit)) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then ((λx . ⟨enc⟩ (π1 x, π2 x)) : (Public * Public) -> Public)
                  else (
                    let c = (λx . ⟨rand⟩ (zero (π2 x), ["0"]) : (Data betaK * Data betaM) -> Public) in
                    (λx . ⟨rand⟩ (zero (π2 x), ["0"])) : (Data betaK * Data betaM) -> Public) :
                  corr (betaK) ? (Public * Public) -> Public : (Data betaK * Data betaM) -> Public))
    in
    pack (Data betaK, ⟨k, (corr_case betaK in enc')⟩)
    ⊢
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK * corr (betaK) ? (Public * Public) -> Public : (alphaK * Data betaM) -> Public))) :=
    by
    tc_man (
      try simp
      auto_solve
    )

theorem enc_ty2 :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ;
      pack (Unit, *)
      ⊢
      (∃ alphaK <: Unit . alphaK)) :=
    by
    tc_man (
      auto_solve
    )
