import OwlLean.TypeChecker.OwlComplete
import OwlLean.CryptoPrims.Utils

-- tau <: Data lM
-- AAD <: Data ⊥
-- alpha <: Data lK
#ty AEAD_inner [lK, lM] [] [tau, alphaK, AAD] :=
   { key : alphaK,
     get_nonce : unit -> Public,
     inc_nonce : unit -> unit,
     enc : (alphaK * tau * AAD) -> Public,
     dec : if corr (lK) then (Public * Public * Public * Public) -> ((Public * Public) + unit) else (alphaK * Public * Public * Public) -> ((tau * AAD) + unit)
     }

#ty AEAD [lK, lM] [] [tau, AAD] :=
    (∃ alphaK <: (Data lK) .
       ($ AEAD_inner [lK, lM] [] [tau, alphaK, AAD]))

-- Similar to the AuthEnc scheme in AuthEnc.lean, but models stateful AEAD (authenticated encryption with authenticated data).
-- The encryptor must also supply an AEAD value.
-- There is also a nonce cell (hidden behind a reference). The AEAD interface allows the user only to obtain the nonce and increment the nonce.
-- The nonce is implicitly incremented and used via encryption.
-- For decryption, the user supplies a nonce.



#tc AEAD_REAL [lK, lM ⊏ lK, corr (lK)] [] [tau <: Data lM, AAD <: Data ⊥] [] := ⊢ {
    let rnd = sample secparam in
    let k : Data lK = ⟦genKey⟧ (rnd) in
    let nonce_cell : Ref Public = alloc (0 : Public) in
    let get_nonce : unit -> Public = λ _ => !nonce_cell in
    let inc_nonce : unit -> unit = λ _ => (nonce_cell := (⟦inc⟧(!nonce_cell))) in
    pack (Data lK,
      { key := k,
        get_nonce := get_nonce,
        inc_nonce := inc_nonce,
        enc := λ (x : (Data lK * tau * AAD)) : Public =>
          let (k, m, aad) = x in
          let n = get_nonce() in
          inc_nonce();
          ⟦aead_enc⟧(k, ((m : Data lM)), (aad : Data ⊥), n),
        dec := λ (x : (Public * Public * Public * Public)) : ((Public * Public) + unit) =>
          let (k, c, n, aad) = x in
          let decResult = ⟦dec⟧(k, c, n, aad) in
          if ⟦isError⟧(decResult) then ı2 () else ı1 ⟨⟦extractMsg⟧(decResult), ⟦extractAAD⟧(decResult)⟩
      })
} : $ AEAD [lK, lM] [] [tau, AAD]


#tc AEAD_IDEAL [lK, lM ⊏ lK] [] [tau <: Data lM, AAD <: Data ⊥] [] := ⊢ {
    if corr (lK) then
      $ AEAD_REAL [lK, lM] [] [tau, AAD] []
    else
      let rnd = sample secparam in
      let k : Data lK = ⟦genKey⟧ (rnd) in
      let L = mk_map (tau * AAD) in
      let nonce_cell : Ref Public = alloc (sample secparam) in
      let get_nonce : unit -> Public = λ _ => !nonce_cell in
      let inc_nonce : unit -> unit = λ _ => (nonce_cell := (⟦inc⟧(!nonce_cell))) in
      let enc = λ (x : (Data lK * tau * AAD)) : Public =>
        let (k, m, aad) = x in
        let n = get_nonce() in
        inc_nonce();
        let c = sample (zero (m : Data lM)) in
        set_map (tau * AAD) L (⟦concat⟧(n, c)) ⟨m, aad⟩;
        c
      in
      admit
      /-
      let rnd = sample secparam in
      let k : Data lK = ⟦genKey⟧ (rnd) in
      let L = mk_map (tau * AAD) in
      let nonce_cell : Ref Public = alloc (sample secparam) in
      type Key = Data lK in
      let get_nonce' : unit -> Public = λ (_ : unit) : Public => !nonce_cell in
      let inc_nonce' : unit -> Public = λ (_ : unit) : Public =>
        let n = ⟦inc⟧(!nonce_cell) in
        get_val n = n in
        nonce_cell := n;
        n in
      let enc' = λ (x : (Data lK * tau * AAD)) : Public =>
        let n = !nonce_cell in
        let c = sample (zero ((π1 (π2 x)) : Data lM)) in
        set_map (tau * AAD) L c ⟨π1 (π2 x), π2 (π2 x)⟩;
        let n' = ⟦inc⟧(n) in
        get_val n' = n' in
        nonce_cell := n';
        c in
      let dec' : if corr (lK) then (Public * Public * Public) -> ((Public * Public) + unit) else (Data lK * Public * Public) -> ((tau * AAD) + unit) =
        corr_case lK in
          if corr (lK) then
            λ (x : (Public * Public * Public)) : ((Public * Public) + unit) =>
              let decResult = ⟦dec⟧(π1 x, π1 (π2 x), π2 (π2 x)) in
              if ⟦isError⟧(decResult) then ı2 () else ı1 ⟨⟦extractMsg⟧(decResult), ⟦extractAAD⟧(decResult)⟩
          else
            λ (x : (Data lK * Public * Public)) : ((tau * AAD) + unit) =>
              get_map (tau * AAD) L (π1 (π2 x)) in
      pack (Key,
        { key := k,
          get_nonce := get_nonce',
          inc_nonce := inc_nonce',
          enc := enc',
          dec := dec'
        })
      -/
} : $ AEAD [lK, lM] [] [tau, AAD]
