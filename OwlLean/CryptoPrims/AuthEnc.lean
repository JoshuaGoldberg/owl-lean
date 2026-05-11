import OwlLean.TypeChecker.OwlComplete

#ty ENC [lK, lM] [] [tau] :=
    (∃ alphaK <: (Data lK) . (alphaK *
                                 ((corr (lK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (lK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + unit)))))



#tc ENC_IDEAL [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM]:=  ⊢ {
    let k = (⟨"genKey"⟩ ("0")) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 ()) in
    let enc' = (corr_case lK in
                (if corr ( lK )
                  then (λ (x : (Public * Public)) : Public =>
                    let (a, b) = x in
                    ⟨"enc"⟩ (a, b))
                  else
                    λ (x : (Data lK * tau )) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data lK)) in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old y))) in
                    c))
    in
    let dec' : corr (lK) ? (Public * Public) -> Public : (Data lK * Public) -> (tau + unit) = (corr_case lK in
               (if corr (lK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data lK * Public)) : (tau + unit) => (!L) (π2 x)))
    in
    pack (Data lK, ⟨k, ⟨(corr_case lK in enc'), dec'⟩⟩) }
    :
    $ ENC [lK, lM] [] [tau]


--- Alternate version with refinement variables ---

#ty ENC' [lK, lM] [] [tau] :=
    (∃ v. (RData lK [v] *
                                 ((corr (lK) ? (Public * Public) -> Public : (RData lK [v] * tau) -> Public) *
                                  (corr (lK) ? (Public * Public) -> Public : (RData lK [v] * Public) -> (tau + unit)))))


#tc ENC_IDEAL' [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM]:=  ⊢ {
    let k = (⟨"genKey"⟩ ("0")) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 ()) in
    let enc' = (corr_case lK in
                (if corr ( lK )
                  then (λ (x : (Public * Public)) : Public =>
                    let (a, b) = x in
                    ⟨"enc"⟩ (a, b))
                  else
                    λ (x : (RData lK [genKey("0")] * tau )) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data lM)) in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old y))) in
                    c))
    in
    let dec' : corr (lK) ? (Public * Public) -> Public : (RData lK [genKey("0")] * Public) -> (tau + unit) = (corr_case lK in
               (if corr (lK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (RData lK [genKey("0")] * Public)) : (tau + unit) => (!L) (π2 x)))
    in
    rpack (genKey("0"), ⟨k, ⟨(corr_case lK in enc'), dec'⟩⟩) }
    :
    $ ENC' [lK, lM] [] [tau]

-- A multi-key assumption


#ty ENC_MULTI [lK, lM] [] [tau] :=
    (∃ alphaK <: (Data lK) . ((unit -> alphaK) *
                                 ((corr (lK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (lK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + unit)))))

-- ENC_MULTI can be filled in similar to ENC_IDEAL by keeping track of the list of keys in scope.
-- We then maintain a mapping from keys and ciphertexts to messages.
-- When we encrypt, we look up the value in the mapping by using the key/message and zero-ed out ciphertext.
