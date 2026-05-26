import OwlLean.TypeChecker.OwlComplete
import OwlLean.CryptoPrims.Utils

/-

  Base assumption:

  BASE_ENC_REAL :=

  let k = gen() in
  (fun x => ⟦enc⟧(k, x), fun x => ⟦dec⟧(k, x))

  ~=

  BASE_ENC_IDEAL :=
   if corr(lK) then
    BASE_ENC_REAL
  else
    let L := alloc [] in
    (fun x =>
      let c = ⟦rand⟧(len(x)) in
      L[c] := x; x,
    fun x => L[x]
    )

  :

  (tau -> Public) * (Public -> Option tau)

-/

-- Typed real functionality:

#ty ENC_inner [lK, lM] [] [tau, alphaK] :=
   { key : alphaK,
     enc : if corr (lK) then (Public * Public) -> Public else (alphaK * tau) -> Public,
     dec : if corr (lK) then (Public * Public) -> (Public + unit) else (alphaK * Public) -> (tau + unit)
     }

#ty ENC [lK, lM] [] [tau] :=
    (∃ alphaK <: (Data lK) .
       ($ ENC_inner [lK, lM] [] [tau, alphaK]))

#tc ENC_REAL [lK ⊒ ⊥, lM ⊏ lK, corr (lK)] [] [tau <: Data lM] [] :=  ⊢ {
    let rnd = sample secparam in
    let k : Data lK   = ⟦genKey⟧ (rnd) in
    pack (Data lK ,
      { key := k,
        enc := λ (x : (Public * Public)) : Public =>
                let (a, b) = x in
                let enc_rnd = sample (⟦enc_rand_bits⟧(secparam)) in
                ⟦enc⟧ (a, (b : Data lM), enc_rnd),
        dec := λ (x : (Data lK  * Public)) : (Public + unit) =>
                let decResult = ⟦dec⟧(π1 x, π2 x) in
                if ⟦isError⟧(decResult) then ı2 () else ı1 ⟦extractMsg⟧(decResult)
      })
} : $ ENC [lK, lM] [] [tau]

/-


  Reduction R:

  fun ENC_DEC =>
    let k = gen() in
    (k, fun k' x => if k = k' then ENC_DEC.1 x, fun k' x => if k = k' then ENC_DEC.2 x)

-/

-- Lemma 1: R BASE_ENC_REAL ~= ENC_REAL


-- Typed ideal functionality:

#tc ENC_IDEAL [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM] [] :=  ⊢ {
    if corr (lK) then
      $ ENC_REAL [lK, lM] [] [tau] []
    else
      let rnd = sample secparam in
      let k : Data lK  = ⟦genKey⟧ (rnd) in
      let L = mk_map tau in
      type Key = Data lK in
      let enc' =
                      λ (x : (Data lK * tau )) : Public =>
                      let c = sample (zero ((π2 x) : Data lM)) in
                      set_map tau L c (π2 x);
                      c

      in
      let dec' =  λ (x : (Data lK * Public)) : (tau + unit) => get_map tau L (π2 x)
      in
      pack (Key,
        { key := k,
          enc := enc',
          dec := dec'
        })
    }
      :
      $ ENC [lK, lM] [] [tau]

-- Lemma 2: not corr(lK) ==> R BASE_ENC_IDEAL ~= ENC_IDEAL

--- Alternate version with refinement variables ---

#ty ENC' [lK, lM] [] [tau] :=
    (∃ v. {
        key : RData lK [v],
        enc : if corr (lK) then (Public * Public) -> Public else (RData lK [v] * tau) -> Public,
        dec : if corr (lK) then (Public * Public) -> (Public + unit) else (RData lK [v] * Public) -> (tau + unit)
      })

/-

  {dec: if corr(lK) then ((Public * Public) -> (Public + Unit)) else ((RData lK [genKey(r0,)] * Public) -> (tau + Unit))
  },
   enc: if corr(lK) then ((Public * Public) -> Public) else ((RData lK [genKey(r0,)] * tau) -> Public) },
   key: RData (⊥ ⊔ _) [genKey(_uniq.54682,)]} <:
   {dec: if corr(_) then ((Public * Public) -> (Public + Unit)) else ((RData _ [genKey(r0,)] * Public) -> (X0 + Unit)) },
   enc: if corr(_) then ((Public * Public) -> Public) else ((RData _ [genKey(r0,)] * X0) -> Public) },
   key: RData _ [genKey(r0,)]}


-/

#tc ENC_IDEAL' [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM] [] :=  ⊢ {
    let rnd : ∃x. RData lK [x] = (sample secparam : Data lK) in
    get_val rnd = rnd in
    let k = ⟦genKey⟧(rnd) in
    let L = mk_map tau in
    let enc' = (corr_case lK in
                (if corr ( lK )
                  then (λ (x : (Public * Public)) : Public =>
                    let (a, b) = x in
                    let enc_rnd = sample (⟦enc_rand_bits⟧(secparam)) in
                    ⟦enc⟧ (a, b, enc_rnd))
                  else
                    λ (x : (RData lK [⟦genKey⟧(rnd)] * tau )) : Public =>
                    let c = sample (zero ((π2 x) : Data lM)) in
                    set_map tau L c (π2 x);
                    c))
    in
    let dec' : if corr (lK) then (Public * Public) -> (Public + unit) else (RData lK [⟦genKey⟧(rnd)] * Public) -> (tau + unit) = (corr_case lK in
               (if corr (lK) then λ (x : (Public * Public)) : Public + unit =>
                   let decResult = ⟦dec⟧(π1 x, π2 x) in
                   if ⟦isError⟧(decResult) then ı2 () else ı1 ⟦extractMsg⟧(decResult)
                else λ (x : (RData lK [⟦genKey⟧(rnd)] * Public)) : (tau + unit) => get_map tau L (π2 x)))
    in
    rpack (⟦genKey⟧(rnd), {
      key := k,
      enc := (corr_case lK in enc'),
      dec := dec'
    })
    }
    :
    $ ENC' [lK, lM] [] [tau]
