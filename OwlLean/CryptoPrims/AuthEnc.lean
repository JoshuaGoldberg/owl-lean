import OwlLean.TypeChecker.OwlComplete

-- version with existential types

#tc ENC_FUNC := ⊢ {
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ ("0", "0") : Data betaK ) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 ()) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau )) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), "0") in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old [y]))) in
                    c))
    in
    let dec' : corr (betaK) ? (Public * Public) -> Public : (Data betaK * Public) -> (tau + unit) = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + unit) => (!L) [π2 x]))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), dec'⟩⟩)
    }
    :
    ∀ betaK ⊒ ⊥ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + unit)))))
    by {
      unfold sideConditions

      simp

      grind
    }

-- version with refinement types

def ENC_R := OwlTy_with [betaK] [] [tau] {
  ∃ x. (RData betaK [x] * ((corr (betaK) ? (Public * Public) -> Public : (RData betaK [x] * tau) -> Public) *
                                          (corr (betaK) ? (Public * Public) -> Public : (RData betaK [x] * Public) -> (tau + unit))))
}


#tc ENC_FUNC' := ⊢ {
    Λβ betaK.
    Λβ betaM.
    Λ tau.
    let k : ∃x. RData betaK [x] =  (⟨"genKey"⟩ ("0", "0") : Data betaK ) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 ()) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau )) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), "0") in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old [y]))) in
                    c))
    in
    let dec' : corr (betaK) ? (Public * Public) -> Public : (Data betaK * Public) -> (tau + unit) = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + unit) => (!L) [π2 x]))
    in
    rpack (val(k), ⟨k, ⟨(corr_case betaK in enc'), dec'⟩⟩)
    -- TOOD: if I expanded the above to "let mod : ... = rpack ... in mod", it won't work, because we
    -- would have the subtype t <: ∃ x. t', which would require us to find a unifier.
} :
  ∀ betaK ⊒ ⊥ .
  ∀ betaM ⊏ betaK .
  ∀ tau <: Data betaM .
  $ ENC_R [betaK] [tau]
  by {
      unfold sideConditions

      simp


      grind

  }
