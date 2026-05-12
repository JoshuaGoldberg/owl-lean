import OwlLean.TypeChecker.OwlComplete
import OwlLean.CryptoPrims.AuthEnc

set_option maxRecDepth 20000

#ty party_type [] [] [] := ((Public -> ((unit -> unit) -> unit)) -> ((Public -> unit) -> unit) -> unit)

#tc run_protocol_client_server
   [lM ⊒ ⊥, lKL ⊐ lM, lKH ⊐ lKL]
   []
   [aPSK <: Data lKH, aKX <: Data lKL, aX <: Data lM]
   [ encPSK : ($ ENC_inner [lKH, lKL] [] [aKX, aPSK]),
     encKX : ($ ENC_inner [lKL, lM] [] [Data lM, aKX]),
     x : Data lM ]
   := ⊢ {
  let server : ($ party_type [] [] []) =
    λ send =>
    λ recv =>
      let enc_psk = π1 (π2 encPSK) in
      let psk = π1 encPSK in
      let dec_kx = π2 (π2 encKX) in
      let key_x = π1 encKX in
      let ct1 = corr_case lKH in enc_psk ⟨psk, key_x⟩ in
      (send ct1) (λ (_ : unit) : unit =>
        recv (λ (ct2 : Public) : unit =>
          corr_case lKL in
          case dec_kx ⟨key_x, ct2⟩ with
          | inl _ => ()
          | inr _ => ()))
  in
  let client : ($ party_type [] [] []) =
    λ send =>
    λ recv =>
      let dec_psk = π2 (π2 encPSK) in
      let enc_kx = π1 (π2 encKX) in
      let psk = π1 encPSK in
      recv (λ (ct1 : Public) : unit =>
        corr_case lKH in
        case dec_psk ⟨psk, ct1⟩ with
        | inl key_x' =>
          let ct2 = corr_case lKL in (enc_kx ⟨key_x', x⟩) in
          (send ct2) (λ (_ : unit) : unit => ())
        | inr _ => ())
  in
  λ (_ : unit) : (Public * Public) -> Public =>
    let s2c_k   : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
    let s2c_out : (Ref Public) = alloc ("" : Public) in
    let c2s_k : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
    let c2s_out : (Ref Public) = alloc ("" : Public) in

    let send_server : (Public -> (unit -> unit) -> unit) =
      λ (v : Public) : ((unit -> unit) -> unit) =>
      λ (k : (unit -> unit)) : unit =>
        (s2c_out := v) ;
        (s2c_k := (λ (_ : Public) : unit => k ())) in

    let recv_server : (Public -> unit) -> unit =
      λ (k : (Public -> unit)) : unit =>
        (c2s_k := k) in

    let recv_client : (Public -> unit) -> unit =
      λ (k : (Public -> unit)) : unit =>
        (s2c_k := k) in

    let send_client : (Public -> (unit -> unit) -> unit) =
      λ (v : Public) : ((unit -> unit) -> unit) =>
      λ (k : (unit -> unit)) : unit =>
        (c2s_out := v) ;
        k () in

    ((server send_server) recv_server) ;
    ((client send_client) recv_client) ;

    (λ (args : (Public * Public)) : Public =>
      let (b, v) = args in
        if b then
          let _ = ((!s2c_k) v) in !s2c_out
        else
          let _ = ((!c2s_k) v) in !c2s_out)
} :
  unit -> ((Public * Public) -> Public)
