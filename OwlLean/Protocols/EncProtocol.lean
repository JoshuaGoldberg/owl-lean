import OwlLean.TypeChecker.OwlComplete
import OwlLean.CryptoPrims.AuthEnc

set_option maxRecDepth 20000

#ty party_type [] [] [] := ((Public -> ((unit -> unit) -> unit)) -> ((Public -> unit) -> unit) -> unit)

#owl {
  label lM ⊒ ⊥
  label lKL ⊐ lM
  label lKH ⊐ lKL

  type aX <: Data lM

  -- Here we assume we have the unpacked encryption.
  -- We could also directly manipulate the packed one (the one coming from the cryptographic assumption)
  -- but then we wouldn't get it at the top level
  type aKX <: Data lKL
  assume encKX : ($ ENC_inner [lKL, lM] [] [aX, aKX])

  type aPSK <: Data lKH
  assume encPSK : ($ ENC_inner [lKH, lKL] [] [aKX, aPSK])

  def server : ($ party_type [] [] []) :=
    λ send =>
    λ recv =>
      let ct1 = corr_case lKH in (encPSK ^. enc) ⟨encPSK ^. key, encKX ^. key⟩ in
      send ct1 (λ (_ : unit) : unit =>
        recv (λ (ct2 : Public) : unit =>
          corr_case lKL in
          case (encKX ^. dec) ⟨encKX ^. key, ct2⟩ with
          | inl _ => ()
          | inr _ => ()))

  def client : aX -> ($ party_type [] [] []) :=
    λ x =>
      λ send =>
      λ recv =>
        recv (λ (ct1 : Public) : unit =>
          corr_case lKH in
          case (encPSK ^. dec) ⟨encPSK ^. key, ct1⟩ with
          | inl key_x' =>
            let ct2 = corr_case lKL in (encKX ^. enc) ⟨key_x', x⟩ in
            (send ct2) (λ (_ : unit) : unit => ())
          | inr _ => ())

  def run_protocol : aX -> (Public * Public) -> Public :=
    λ x =>
      let s2c_k   : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
      let s2c_out : (Ref Public) = alloc ("" : Public) in
      let c2s_k : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
      let c2s_out : (Ref Public) = alloc ("" : Public) in

      let send_server : (Public -> (unit -> unit) -> unit) =
        λ (v : Public) : ((unit -> unit) -> unit) =>
        λ (k : (unit -> unit)) : unit =>
          (s2c_out := v) ;
          (s2c_k := (λ (_ : Public) : unit => k ()))
      in

      let recv_server : (Public -> unit) -> unit =
        λ (k : (Public -> unit)) : unit =>
          (c2s_k := k)
      in

      let recv_client : (Public -> unit) -> unit =
        λ (k : (Public -> unit)) : unit =>
          (s2c_k := k)
      in

      let send_client : (Public -> (unit -> unit) -> unit) =
        λ (v : Public) : ((unit -> unit) -> unit) =>
        λ (k : (unit -> unit)) : unit =>
          (c2s_out := v) ;
          k ()
      in

      server send_server recv_server;
      client x send_client recv_client;

      λ (args : (Public * Public)) : Public =>
        let (b, v) = args in
          if b then
            let _ = ((!s2c_k) v) in !s2c_out
          else
            let _ = ((!c2s_k) v) in !c2s_out


}


--- State Machine version --
----------


#ty StateMachine := ∃ S <: Any . (S * ((S * Public) -> (S * Public)))

#owl {
  label lM ⊒ ⊥
  label lKL ⊐ lM
  label lKH ⊐ lKL

  type aX <: Data lM

  type aKX <: Data lKL
  assume encKX : ($ ENC_inner [lKL, lM] [] [aX, aKX])

  type aPSK <: Data lKH
  assume encPSK : ($ ENC_inner [lKH, lKL] [] [aKX, aPSK])

  def run_sm := λ (m : $ StateMachine [] [] [] ) : (Public -> Public) =>
    unpack m as (S, contents) in
    let state_ref = alloc (π1 contents) in
    let step = π2 contents in
    λ (input: Public) : Public =>
      let result = step ⟨!state_ref, input⟩ in
      (state_ref := π1 result) ;
      π2 result

  def run_two_sm := λ (a : $ StateMachine [] [] [] ) : ($ StateMachine [] [] [] -> (Public * Public) -> Public) =>
    λ (b : $ StateMachine [] [] [] ) : ((Public * Public) -> Public) =>
      let A = (run_sm a) in
      let B = (run_sm b) in
      λ (val : (Public * Public)) : Public =>
        let (det, msg) = val in
        if (⟨"eq"⟩ (det, "0")) then
          A msg
        else
          B msg

  def alice_sm : aX ->  $ StateMachine [] [] [] :=
   λ msg =>
    pack (Public,
        ⟨"0",
          (λ (args : (Public * Public)) : (Public * Public) =>
            let (state, input) = args in
            if (⟨"eq"⟩ (state, "0")) then
              let ciphertext1 = (corr_case lKH in (encPSK ^. enc) ⟨encPSK ^. key, encKX ^. key⟩) in
                ⟨"1", ciphertext1⟩
            else if (⟨"eq"⟩ (state, "1")) then
              let ciphertext2 = (corr_case lKL in (encKX ^. enc) ⟨encKX ^. key, msg⟩) in
                    ⟨"10", ciphertext2⟩
            else
              ⟨"10", ""⟩)
        ⟩)

  def bob_sm : $ StateMachine [] [] [] :=
    let key_store : Ref (unit + (corr (lKL)? Public : aKX)) = alloc (
      let v : unit + (corr (lKL)? Public : aKX) = ı1 () in
      v
      )
    in
    pack (Public,
      ⟨"0",
        (λ (args : (Public * Public)) : (Public * Public) =>
          let (state, input) = args in
          if (⟨"eq"⟩ (state, "0")) then
            corr_case lKH in
            case (encPSK ^. dec) ⟨encPSK ^. key, input⟩ with
            | inl key_low' =>
                corr_case lKL in
                (key_store := (ı2 key_low' : unit + (corr (lKL)? Public : aKX))) ;
                ⟨"1", "0"⟩
            | inr _fail =>
                ⟨"10", "1"⟩
          else if (⟨"eq"⟩ (state, "1")) then
            let stored_key = (!key_store) in
            case stored_key with
            | inl _ => ⟨"10", "err"⟩
            | inr k =>
              corr_case lKL in
              case (encKX ^. dec) ⟨k, input⟩ with
              | inl _ =>
                ⟨"10", "0"⟩
              | inr _ =>
                ⟨"10", "1"⟩
          else
            ⟨"10", ""⟩)⟩
    )

  def protocol : aX -> (Public * Public) -> Public :=
    λ x =>
      let a = (alice_sm x) in
      let b = (bob_sm) in
      ((run_two_sm a) b)

}
