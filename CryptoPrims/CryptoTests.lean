import Lean
import OwlLean.TypeChecker.OwlComplete
import OwlLean.TypeChecker.TcSimple

open Lean Meta Elab Tactic

open OwlTypecheck


-- "[0]" represents garbage values not needed for computation
/-
theorem enc_i :
  ( · ; · ; · ; · ⊢
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    let L = alloc (λ (null : Public) : (tau + Unit) => ı2 *) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau)) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), ["0"]) in
                    let L_old = (! L) in
                    let sc = L := (λ (y : Public) : (tau + Unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else L_old [y]) in
                    c))
    in
    let dec' = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + Unit) => (!L) [π2 x]))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), (corr_case betaK in dec')⟩⟩)
    :
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
    apply OwlTypecheck.infer_sound


    unfold OwlTypecheck.infer




    rw [OwlTypecheck.infer]

-/


open EStateM

theorem enc_ty2 :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ⊢
      pack (Unit, *)
      :
      (∃ alphaK <: Unit . alphaK)) :=
    by
      apply OwlTc.infer_sound
      dsimp [OwlTc.infer, OwlTc.check_subtype, OwlTc.has_type_infer]
      simp [EStateM.run]
      simp [pure, EStateM.pure]





theorem test_let_2 :
  ( · ; · ; · ; · ⊢
      let (x, y) = ⟨* , ["0"]⟩ in
      y
      :
      Public) :=
    by
      apply infer_sound
      simp
      dsimp [infer]
      dsimp [check_subtype]
      simp

theorem test_let_3 :
  ( · ; · ; · ; · ⊢
      let (x, y, z) = ⟨⟨* , *⟩ , ⟨*, ["0"]⟩⟩ in
      z
      :
      Public) :=
    by
    tc_man (
      try simp
      try auto_solve
    )

theorem enc_ty_contra :
  ((betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      (if corr (betaK) then ((λ x => *) : Public -> Unit) else ((λ x => x) : Data betaC -> Data betaC))
      :
      (Public -> Unit)) :=
    by
    tc_man (
      try simp
      auto_solve
    )

theorem enc_length_test :
  ( (betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ a => λ x => λ x => λ b =>
      λ x => λ x => λ y => λ x => λ h => λ x => λ a => λ x => λ x => λ x => λ x => λ x => λ x => λ x =>
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ z => λ x => λ x => λ x => λ x => λ x => ⟨a, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨z, x⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      :
      (Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->

       ((Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * Public))))))))))))) :=
    by
    tc_man (
      try simp
      auto_solve
    )


theorem enc_r :
  ( (betaK, betaM) ; (corr(betaK)) ; (tau <: Data betaM) ; · ⊢
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    pack (Data betaK, ⟨k, ⟨λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x),
                           λ (y : (Public * Public)) : Public => ⟨"dec"⟩ (π1 y, π2 y)⟩⟩)
    :
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * (Data betaM)) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
      simp
      apply infer_sound
      dsimp [infer]
      dsimp [check_subtype]


theorem enc_unpack :
  ( (betaK, betaM ⊑ betaK) ; · ; (tau <: Data betaM) ;
  (E => (∃ alphaK <: (Data betaK) . (alphaK *
                                     ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                      (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit))))),
   x => tau) ⊢
    (corr_case betaK in
     unpack E as (alpha, ked) in
     (π1 (π2 ked)) [⟨(π1 ked), x⟩])
    :
    Public) :=
    by
    tc_man (
      try simp
      auto_solve
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
                          (corr (l2) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ⊢
    (corr_case l3 in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       (π1 (π2 ked1)) [⟨(π1 ked1), (π1 ked2)⟩])
    :
    Public) := by
      apply OwlTc.infer_sound
      dsimp [OwlTc.has_type_infer, OwlTc.infer]
      dsimp [EStateM.run]
      simp




-- partial
theorem enc_sig :
  ( · ; · ; · ; · ⊢
    Λβ betaK .
    Λ tau .
    corr_case betaK in
    (if corr (betaK) then
      ((let sk = ⟨"genSK"⟩(["0"], ["0"]) in
      let vk = ⟨"vk_of_sk"⟩(sk, ["0"]) in
      pack(Public, pack (Public, ⟨sk, ⟨vk,
                    ⟨((λ xy => ⟨"sign"⟩(π1 xy, π2 xy)) : (Public * Public) -> Public),
                     ((λ xyz => ⟨"vrfy"⟩(π1 xyz, π1 (π2 xyz))) : (Public * (Public * Public)) -> Public)⟩⟩⟩))) :
                     ∃ alpha <: Data betaK .
                     ∃ beta <: Public .
                     (alpha *
                     (beta *
                     ((corr (betaK) ? ((Public * Public) -> Public) : ((alpha * tau) -> Public)) *
                     (corr (betaK) ? ((Public * (Public * Public)) -> Public) : ((beta * (Public * Public)) -> (tau + Unit)))))))
    else
      ((let sk = ⟨"genSK"⟩(["0"], ["0"]) in
      let pk = ⟨"vk_of_sk"⟩(["0"], ["0"]) in
      let L = ((alloc (λ (null : (Public * Public)) : (tau + Unit) => (ı2 *))) : Ref ((Public * Public) -> (tau + Unit))) in
      let sign =  ((λ (skm : (Data betaK * tau)) : Public =>
                  let sig = (⟨"rand"⟩(((π2 skm) : Public), ["0"]) : Public) in
                  let L_old = (! L) in
                  let action =  (L := (λ (msig' : (Public * Public)) : (tau + Unit) => if ⟨"and"⟩(⟨"eq"⟩(π2 skm, π2 msig'), ⟨"eq"⟩(sig, π2 msig'))
                                                then (ı1 (π2 skm))
                                                else L_old [msig']))
                  in
                  sig) : (((Data betaK * tau) -> Public)))
      in
      let vrfy = ((λ vkmsig =>
                  (! L) [⟨π1 (π2 vkmsig), π2 (π2 vkmsig)⟩]) : ((Public * (Public * Public)) -> (tau + Unit))) in
      pack(Data betaK, pack(Public, ⟨sk, ⟨pk, ⟨sign, vrfy⟩⟩⟩))) :
      ∃ alpha <: Data betaK .
      ∃ beta <: Public .
      (alpha *
      (beta *
      ((corr (betaK) ? ((Public * Public) -> Public) : ((alpha * tau) -> Public)) *
       (corr (betaK) ? ((Public * (Public * Public)) -> Public) : ((beta * (Public * Public)) -> (tau + Unit))))))))
    :
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
      auto_solve_fast
    )

    -- the issue here is that just because tau <: public, does that mean public <: tau?

theorem enc_layered2_high_low :
  ( (L_sec, L_low ⊒ L_sec, L_high ⊒ L_low) ; · ; (a <: Data L_sec, b <: Data L_low) ;
  (E1 => (∃ alphaK <: (Data L_low) .
                        (alphaK *
                         ((corr (L_low) ? (Public * Public) -> Public : (alphaK * (Data L_sec)) -> Public) *
                          (corr (L_low) ? (Public * Public) -> Public : (alphaK * Public) -> (a + Unit))))),
   E2 => (∃ alphaK <: (Data L_high) .
                        (alphaK *
                         ((corr (L_high) ? (Public * Public) -> Public : (alphaK * (Data L_low)) -> Public) *
                          (corr (L_high) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ⊢
    (corr_case L_low in
      (corr_case L_high in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       ((λ x =>
        let c1 = ((π1 (π2 ked1)) [⟨(π1 ked1), x⟩] : Public) in
        let c2 = ((π1 (π2 ked2)) [⟨(π1 ked2), (π1 ked1)⟩] : Public) in
        ⟨"combine"⟩(c1, c2)) : ((Data L_sec) -> Public))))
    :
    ((Data L_sec) -> Public)) :=
    by
    tc_man (
      try simp
      auto_solve_fast
    )

-/
