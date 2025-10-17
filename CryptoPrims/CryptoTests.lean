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

@[app_unexpander Owl.Lattice.bot]
def unexpOwlBot : Unexpander
| `($_ $_) => `(⊥)
| _        => throw ()

-- non functional
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

-- non functional
def genSk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def pk_of_sk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def vk_of_sk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def and_op : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def combine : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def sign : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def vrfy : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- "[0]" represents garbage values not needed for computation
theorem enc_i :
  ( · ; · ; · ; · ;
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨genKey⟩ (["0"], ["0"]) : Data betaK) in
    let L = (alloc (λ null . ı2 *) : Ref (Public -> (tau + Unit))) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then ((λx . ⟨enc⟩ (π1 x, π2 x)) : (Public * Public) -> Public)
                  else
                    (λx .
                    let c = ⟨rand⟩ (zero ((π2 x) : Data betaM), ["0"]) in
                    let L_old = (! L) in
                    let sc = L := (λ y . if ⟨eq⟩(y, c) then ı1 (π2 x) else L_old [y]) in
                    c : (Data betaK * tau) -> Public)))
    in
    let dec' = (corr_case betaK in
               (if corr (betaK) then (λ x . ⟨dec⟩(π1 x, π2 x) : (Public * Public) -> Public)
                else (λ x . (!L) [π2 x] : (Data betaK * Public) -> (tau + Unit))))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), (corr_case betaK in dec')⟩⟩)
    ⊢
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
    tc_man (
      try simp
      auto_solve_fast
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

theorem enc_r :
  ( (betaK, betaM) ; (corr(betaK)) ; (tau <: Data betaM) ; · ;
    let k = (⟨genKey⟩ (["0"], ["0"]) : Data betaK) in
    pack (Data betaK, ⟨k, ⟨(λ x . ⟨enc⟩ (π1 x, π2 x) : (Public * Public) -> Public),
                          (λ y . ⟨dec⟩ (π1 y, π2 y) : (Public * Public) -> Public)⟩⟩)
    ⊢
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * (Data betaM)) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
    tc_man (
      try simp
      auto_solve_fast
    )

theorem enc_unpack :
  ( (betaK, betaM ⊑ betaK) ; · ; (tau <: Data betaM) ;
  (E => (∃ alphaK <: (Data betaK) . (alphaK *
                                     ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                      (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit))))),
   x => tau) ;
    (corr_case betaK in
     unpack E as (alpha, ked) in
     (π1 (π2 ked)) [⟨(π1 ked), x⟩])
    ⊢
    Public) :=
    by
    tc_man (
      try simp
      try auto_solve_fast
    )

theorem enc_layered :
  ( (l1, l2 ⊒ l1, l3 ⊒ l2) ; · ; (a <: Data l2, b <: Data l1) ;
  (E1 => (∃ alphaK <: (Data l3) .
                        (alphaK *
                         ((corr (l3) ? (Public * Public) -> Public : (alphaK * (Data l2)) -> Public) *
                          (corr (l3) ? (Public * Public) -> Public : (alphaK * Public) -> (a + Unit))))),
   E2 => (∃ alphaK <: (Data l2) .
                        (alphaK *
                         ((corr (l2) ? (Public * Public) -> Public : (alphaK * (Data l1)) -> Public) *
                          (corr (l2) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ;
    (corr_case l3 in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       (π1 (π2 ked1)) [⟨(π1 ked1), (π1 ked2)⟩])
    ⊢
    Public) :=
    by
    tc_man (
      try simp
      try auto_solve_fast
    )

-- partial
theorem enc_sig :
  ( · ; · ; · ; · ;
    Λβ betaK .
    Λ tau .
    corr_case betaK in
    (if corr (betaK) then
      let sk = ⟨genSk⟩(["0"], ["0"]) in
      let vk = ⟨vk_of_sk⟩(sk, ["0"]) in
      pack(Public, pack (Public, ⟨sk, ⟨vk,
                    ⟨((λ xy . ⟨sign⟩(π1 xy, π2 xy)) : (Public * Public) -> Public),
                     ((λ xyz . ⟨vrfy⟩(π1 xyz, π1 (π2 xyz))) : (Public * (Public * Public)) -> Public)⟩⟩⟩))
    else
      let sk = ⟨genSk⟩(["0"], ["0"]) in
      let pk = ⟨pk_of_sk⟩(sk, ["0"]) in
      let L = (alloc (λ null . ı2 *) : Ref ((Public * Public) -> (tau + Unit))) in
      let sign =  ((λ skm .
                  let sig = (⟨rand⟩(π2 skm, ["0"]) : Public) in
                  let L_old = (! L) in
                  let action = (L := (λ msig' . if ⟨and_op⟩(⟨eq⟩((π2 skm), π2 msig'), ⟨eq⟩(sig, π2 msig'))
                                                then (ı1 (π2 skm))
                                                else L_old [msig']))
                  in
                  sig) : (((Data betaK * tau) -> Public)))
      in
      let vrfy = ((λ vkmsig .
                  (! L) [⟨π1 (π2 vkmsig), π2 (π2 vkmsig)⟩]) : ((Public * (Public * Public)) -> (tau + Unit))) in
      pack(Data betaK, pack(Public, ⟨sk, ⟨pk, ⟨(corr_case betaK in sign), (corr_case betaK in vrfy)⟩⟩⟩)))
    ⊢
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ tau <: Public .
    ∃ alpha <: Data betaK .
    ∃ beta <: Public .
    (alpha *
    (beta *
    ((corr (betaK) ? ((Public * Public) -> Public) : ((alpha * tau) -> Public)) *
     (corr (betaK) ? ((Public * (Public * Public)) -> Public) : ((beta * (Public * Public)) -> (tau + Unit))))))
    ) :=
    by
    tc_man (
      try simp
      try auto_solve_fast
    )

    -- the issue here is that just because tau <: public, does that mean public <: tau?

theorem enc_layered2 :
  ( (L_sec, L_low ⊒ L_sec, L_high ⊒ L_low) ; · ; (a <: Data L_sec, b <: Data L_low) ;
  (E1 => (∃ alphaK <: (Data L_low) .
                        (alphaK *
                         ((corr (L_low) ? (Public * Public) -> Public : (alphaK * (Data L_sec)) -> Public) *
                          (corr (L_low) ? (Public * Public) -> Public : (alphaK * Public) -> (a + Unit))))),
   E2 => (∃ alphaK <: (Data L_high) .
                        (alphaK *
                         ((corr (L_high) ? (Public * Public) -> Public : (alphaK * (Data L_low)) -> Public) *
                          (corr (L_high) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ;
    (corr_case L_low in
      (corr_case L_high in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       ((λ x .
        let c1 = ((π1 (π2 ked1)) [⟨(π1 ked1), x⟩] : Public) in
        let c2 = ((π1 (π2 ked2)) [⟨(π1 ked2), (π1 ked1)⟩] : Public) in
        ⟨combine⟩(c1, c2)) : ((Data L_sec) -> Public))))
    ⊢
    ((Data L_sec) -> Public)) :=
    by
    tc_man (
      try simp
      try auto_solve_fast
    )
