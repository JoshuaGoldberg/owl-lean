import OwlLean.TypeChecker.OwlComplete
import OwlLean.OwlLang.Owl
import OwlLean.CryptoPrims.Utils


#ty PKE_inner [lK, lM] [] [tau, sk, pk] := {
  sk : sk,
  pk : pk,
  enc : if corr (lK) then (Public * Public) -> Public else (pk * tau) -> Public,
  dec : if corr (lK) then (Public * Public) -> (Public + unit) else
    (sk * Public) ->
    ((tau ∪ Public) +  unit)
}

#ty PKE [lK, lM] [] [tau] :=
  ∃ sk <: Data lK.
    ∃ pk <: Public.
      ($ PKE_inner [lK, lM] [] [tau, sk, pk])

#tc PKE_IDEAL [lK ⊒ ⊥, lM ⊏ lK] [] [tau <: Data lM] [] := ⊢ {
  let sk = (⟦genSK⟧((secparam : Data lK))) in
  get_val sk = sk in
  type SK = RData lK [sk] in
  let pk = (⟦genPK⟧((secparam : Data ⊥))) in
  get_val pk = pk in
  type PK = RData ⊥ [pk] in

  let L = mk_map (tau) in

  let enc : if corr (lK) then (Public * Public) -> Public else (PK * tau) -> Public =
    if corr (lK) then
      λ (x : (Public * Public)) : Public =>
        let (a, b) = x in
        ⟦pkenc⟧(a, b)
    else
      λ (x : (PK * tau)) : Public =>
        let fake_pk = (⟦genPK⟧((secparam : Data ⊥))) in
        let c = ⟦pkenc⟧(fake_pk, zero (π2 x : Data lM)) in
        set_map tau L c (π2 x);
        c
  in

  let dec : if corr (lK) then (Public * Public) -> (Public + unit) else (SK * Public) -> ((tau ∪ Public) + unit) =
    if corr (lK) then
      λ (x : (Public * Public)) : (Public + unit) =>
        let (a, b) = x in
        ⟦dec⟧(a, b)
    else
      λ (x : (SK * Public)) : ((tau ∪ Public) + unit) =>
        let o = get_map tau L (π2 x) in
        case o with
        | inl v => admit
        | inr _ => admit
  in

  pack (SK,
   pack (PK,
     {
      sk := sk,
      pk := pk,
      enc := enc,
      dec := dec
     }
   ) )
} : $ PKE [lK, lM] [] [tau]
