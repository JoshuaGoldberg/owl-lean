import OwlLean.TypeChecker.OwlComplete

set_option maxHeartbeats 1000000
set_option trace.profiler true
set_option trace.profiler.threshold 0

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
    tc_man (
      try simp
      auto_solve
    )

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
