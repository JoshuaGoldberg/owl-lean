
import OwlLean.TypeChecker.OwlComplete
import OwlLean.OwlLang.Owl
import OwlLean.CryptoPrims.Utils



#ty ENC_MULTI [lK, lM] [] [tau] :=
    (∃ alphaK <: Any. {
      genKey : (unit -> alphaK),
      getKey : (alphaK -> Data lK),
      enc : if corr (lK) then (Public * Public) -> Public else (alphaK * tau) -> Public,
      dec : if corr (lK) then (Public * Public) -> (Public + unit) else (alphaK * Public) -> (tau + unit)
    })

#tc ENC_MULTI_REAL [lK ⊒ ⊥, lM ⊏ lK, corr (lK)] [] [tau <: Data lM] [] :=  ⊢ {
    pack (Data lK, {
      genKey := λ (_ : unit) : Data lK => ⟦genKey⟧(sample secparam),
      getKey := λ (k : Data lK) : Data lK => k,
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
        type alphaK = Public * Data lK  in
        let genKey  = λ (_ : unit) : alphaK => ⟨⟦genKey⟧(sample secparam), sample secparam⟩  in
        -- TODO: This doesn't work because maps currently cannot hold secret keys.
        let enc = λ (x : (alphaK * tau)) : Public =>
           let (k, m) = x in
           let (hdl, k) = k in
           let c = sample (zero (m : Data lM)) in
           set_map tau L (⟦concat⟧(hdl, c)) m;
           c
        in
        let dec = λ (x : (alphaK * Public)) : (tau + unit) =>
          let (k, c) = x in
          let (hdl, k) = k in
          case get_map tau L (⟦concat⟧(hdl, c)) with
          | inl m => ı1 m
          | inr _ => ı2 ()
        in
        pack (alphaK, {
          genKey := genKey,
          getKey := λ (k : alphaK) : Data lK => let (_, k) = k in k,
          enc := enc,
          dec := dec
        })

    )
} : $ ENC_MULTI [lK, lM] [] [tau]
