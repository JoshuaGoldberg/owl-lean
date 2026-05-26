
import OwlLean.TypeChecker.OwlComplete
import OwlLean.OwlLang.Owl
import OwlLean.CryptoPrims.Utils



#ty ENC_MULTI [lK, lM] [] [tau] :=
    (∃ alphaK <: Data lK . {
      genKey : (unit -> alphaK),
      enc : if corr (lK) then (Public * Public) -> Public else (alphaK * tau) -> Public,
      dec : if corr (lK) then (Public * Public) -> (Public + unit) else (alphaK * Public) -> (tau + unit)
    })

#tc ENC_MULTI_REAL [lK ⊒ ⊥, lM ⊏ lK, corr (lK)] [] [tau <: Data lM] [] :=  ⊢ {
    pack (Data lK, {
      genKey := λ (_ : unit) : Data lK => ⟦genKey⟧(sample secparam),
      enc := λ (x : (Public * Public)) : Public =>
        let (a, b) = x in
        let enc_rnd = sample (⟦enc_rand_bits⟧(secparam)) in
        ⟦enc⟧(a, b, enc_rnd),
      dec := λ (x : (Public * Public)) : (Public + unit) =>
        let (a, b) = x in
        let decResult = ⟦dec⟧(a, b) in
        if ⟦isError⟧(decResult) then ı2 () else ı1 ⟦extractMsg⟧(decResult)

    })
} : $ ENC_MULTI [lK, lM] [] [tau]

#tc ENC_MULTI_IDEAL [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM] [] :=  ⊢ {
    if corr (lK) then
        $ ENC_MULTI_REAL [lK, lM] [] [tau] []
    else  (
        let L = mk_map tau in
        let genKey  = λ (_ : unit) : Public => ⟦genKey⟧(sample secparam) in
        let enc = λ (x : (Public * tau)) : Public =>
           let (k, m) = x in
           let c = sample (zero (m : Data lM)) in
           set_map tau L (⟦concat⟧(k, c)) m;
           c
        in
        let dec = λ (x : (Public * Public)) : (tau + unit) =>
          let (k, c) = x in
          case get_map tau L (⟦concat⟧(k, c)) with
          | inl m => ı1 m
          | inr _ => ı2 ()
        in
        pack (Public, {
          genKey := genKey,
          enc := enc,
          dec := dec
        })

    )
} : $ ENC_MULTI [lK, lM] [] [tau]
