import OwlLean.TypeChecker.OwlComplete
import OwlLean.OwlLang.Owl
import OwlLean.CryptoPrims.Utils

open Owl


#ty SIG_inner [lK] [] [tau, sk, pk]  :=
  { pk : pk,
    sk : sk,
    sign : corr (lK) ? (Public * Public) -> Public : (sk * tau) -> Public,
    vfy : corr (lK) ? (Public * Public * Public) -> Public : (pk * Public * Public) -> (tau + unit)
  }

#ty SIG [lK] [] [tau] :=
  ∃ sk <: Data lK. ∃ pk <: Public . ($ SIG_inner [lK] [] [tau, sk, pk])

#tc SIG_IDEAL [lK ⊒ ⊥] [] [tau <: Public] [] := ⊢ {
   let sk = (⟦genSK⟧(secparam)) in
   let fake_pk = (⟦genPK⟧(secparam)) in
   let real_pk = (⟦pk_of_sk⟧(sk)) in
   type SK = Data lK in
   type PK = Public in
   let pk = if corr (lK) then real_pk else fake_pk in
   let sigmap = mk_map (tau) in

   let sign = if corr (lK) then
      λ (x : (Public * Public)) : Public =>
        let (m, s) = x in
        let sig = ⟦sign⟧(m, s) in
        sig
      else
        λ (x : (SK * tau)) : Public =>
        let fake_sk : Data ⊥ = (⟦genSK⟧(secparam)) in
        let (_, msg) = x in
        let sig = ⟦sign⟧(fake_sk, (msg : Public)) in
        set_map (tau) sigmap sig msg;
        sig
   in
   let vrfy = if corr (lK) then
      λ (x : (Public * Public * Public)) : Public =>
        let (m, s, v) = x in
        let sig = ⟦vrfy⟧(m, s, v) in
        sig
      else
        λ (x : (PK * Public * Public)) : (tau + unit) =>
        let (_, s, v) = x in
        get_map (tau) sigmap s
    in
   pack (SK, pack (PK, { sk := sk, pk := pk, sign := sign, vfy := vrfy }))
} : $ SIG [lK] [] [tau]
