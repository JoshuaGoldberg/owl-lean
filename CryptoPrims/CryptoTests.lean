import Lean
import OwlLean.TypeChecker.OwlComplete

open Lean Meta Elab Tactic
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000000

open OwlTc

-- New syntax:
-- rpack
-- ∀ r. τ
-- Λr r. e
-- ∃ r. e

-- τ { p }


attribute [simp] Fin.foldr_succ

def sample := OwlTy {
  ∀ l ⊒ ⊥. Public -> Data l
}

#tc tst1 := ⊢ {
  λ f =>
    f ⟨ ⊥ ⟩
}
  :
  ($ sample [] [])
  ->
  (Public -> Data ⊥)
  by {
    unfold sideConditions
    simp
    grind
  }



#tc example_rpack :=  ⊢ {
  let x = "0" in
  rpack ("0", x)
  }
  :
  ∃ x. RData ⊥ [x]
  by {
    unfold sideConditions
    simp
  }

#tc example_rlam0 :=  ⊢ {
  let foo : (∀ r. RData ⊥ [r] -> RData ⊥ [r])  = (Λr r.
    λ (x : RData ⊥ [ r ]) : RData ⊥ [ r ] =>
      x
  )
  in
  foo
}
  :
  ∀ x.
    RData ⊥ [x]
    ->
    RData ⊥ [x]
  by {
      unfold sideConditions
      simp
  }


def tst := OwlTy {
    ∀ x . Public
}

#tc example0 :=  ⊢ {
  "0" } : (Public)  by {
      unfold sideConditions
      simp
      try grind
  }

#tc rexp := ⊢ {
  "0" } : Data ⊥
  by  {
    unfold sideConditions
    simp
    intros
    grind
  }



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
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old y))) in
                    c))
    in
    let dec' : corr (betaK) ? (Public * Public) -> Public : (Data betaK * Public) -> (tau + unit) = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + unit) => (!L) π2 x))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), dec'⟩⟩) }
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



-- Bonus points: make it a record


-- Type represention is a lean TreeMap from String to type
def ENC_Inner := OwlTy_with [lK] [] [tM, tK] {
    ( tK *
        ((corr (lK) ? (Public * Public) -> Public : (tK * tM) -> Public) *
        (corr (lK) ? (Public * Public) -> (Public + unit) : (tK * Public) -> (tM + unit))))
}

def ENC := OwlTy_with [ lK ] [] [ tM ] {
  ∃ alphaK <: (Data lK). $ ENC_Inner [ lK ] [ tM, alphaK ]
}



/-

  A                   B
  --                 ---

        enc(kH, kL)
        enc(kL, m)
        --->



                        --> "ok" or "bad", depending on if decryption succeeded




  A has some state type S_A

  A has a transition function S_A -> Public -> (S_A * Public)


  B has some state type S_B

  B has a transition function S_B -> Public -> (Public * S_B)



  A, B: StateMachine := ∃ S. (S * (S -> Public -> (Public * S)))



  TODO:

  1.
  - Define a function of type StateMachine -> StateMachine -> ((Public * Public) -> Public)
    - First public input: who is running
      - "0" for alice
      - not "0" for bob


    - Second public input: the input to the state machine
    - Output: output from the state machine

    - Need to create references to the internal states

    - Implement in OCaml first?


  2.
  - re-Implement below protocol as state machines


  3.
  - future: beef up protocol


  ----------------
  Option 2 (do this after the above)

  - Give a coroutine semantics to the protocol


  output:
    Public  -- Thing to output
    -> (Unit -> Public)  -- Continuation that is given to the adversary
    -> Public -- "final return value"


  input:
    (Public -> Public)  -- Continuation given to adversary, where input is adv's input from network
    -> Public -- "Final return value"


  Alice:

  let (c1, c2) = do_encrypts () in
  output c1 (fun _ =>
    output c2 (fun _ =>
      return "ok"
    )
  )

  State := (Public -> Public)


  Bob:

  input (fun i =>
    if decrypt_ok(i) then
      output "ok" (fun _ => ())
    else
      output "bad" (fun _ => ())
  )


  ==========


  Along the way:
  - Fix the syntax
  - Fix error messages


  ==========

  - Prove soundness theorems in TcSimple


-/

-- state machine
def StateMachine := OwlTy {
  ∃ S <: Any . (S * ((S * Public) -> (S * Public)))
}

-- state machine execution type
def run_sm_ty := OwlTy {
  $ StateMachine [] [] -> (Public -> Public)
}

def two_sm := OwlTy {
  $ StateMachine [] [] -> $ StateMachine [] [] -> ((Public * Public) -> Public)
}

-- the whole double state machine
#tc_with tc_run_alice_bob := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aKH <: Data lKH, aKL <: Data lKL ; · ;
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL]),
  msg => Data lM
  ⊢
  let run_sm_tm =
    λ (m : $ StateMachine [] []) : (Public -> Public) =>
      unpack m as (S, contents) in
      let state_ref = alloc (π1 contents) in
      let step = π2 contents in
      λ (input: Public) : Public =>
        let result = step ⟨!state_ref, input⟩ in
        (state_ref := π1 result) ;
        π2 result
  in

  let run_two_sm =
    λ (a : $ StateMachine [] []) : ($ StateMachine [] [] -> (Public * Public) -> Public) =>
      λ (b : $ StateMachine [] []) : ((Public * Public) -> Public) =>
      -- generate a single state machine run function
      let A = (run_sm_tm a) in
      -- let's do it again!
      let B = (run_sm_tm b) in
      λ (val : (Public * Public)) : Public =>
        let (det, msg) = val in
        if (⟨"eq"⟩ (det, "0")) then
          A msg
        else
          B msg
  in

  let alice_sm : $ StateMachine [] [] =
  pack (Public,
      ⟨"0",
        (λ (args : (Public * Public)) : (Public * Public) =>
          let enc_high = π1 (π2 encH) in
          let enc_low = π1 (π2 encL) in
          let key_high = π1 encH in
          let key_low = π1 encL in
          let (state, input) = args in
          if (⟨"eq"⟩ (state, "0")) then
            let ciphertext1 = (corr_case lKH in (enc_high ⟨key_high, key_low⟩)) in
              ⟨"1", ciphertext1⟩
          else if (⟨"eq"⟩ (state, "1")) then
            let ciphertext2 = (corr_case lKL in (enc_low ⟨key_low, msg⟩)) in
                  ⟨"10", ciphertext2⟩
          else
            ⟨"10", ""⟩)
      ⟩)
  in

  let bob_sm : $ StateMachine [] [] =
    let key_store : Ref (unit + (corr (lKL)? Public : aKL)) = alloc (
      let v : unit + (corr (lKL)? Public : aKL) = ı1 () in
      v
      )
    in
    pack (Public,
      ⟨"0",
        (λ (args : (Public * Public)) : (Public * Public) =>
          let dec_high = π2 (π2 encH) in
          let dec_low = π2 (π2 encL) in
          let key_high = π1 encH in
          let (state, input) = args in
          if (⟨"eq"⟩ (state, "0")) then
            corr_case lKH in
            case (dec_high ⟨key_high, input⟩) with
            | inl key_low' =>
                corr_case lKL in
                (key_store := (ı2 key_low' : unit + (corr (lKL)? Public : aKL))) ;
                ⟨"1", "0"⟩
            | inr _fail =>
                ⟨"10", "1"⟩
          else if (⟨"eq"⟩ (state, "1")) then
            let stored_key = (!key_store) in
            case stored_key with
            | inl _ => ⟨"10", "err"⟩
            | inr k =>
              corr_case lKL in
              case (dec_low ⟨k, input⟩) with
              | inl _ =>
                ⟨"10", "0"⟩
              | inr _ =>
                ⟨"10", "1"⟩
          else
            ⟨"10", ""⟩)⟩
    )
  in
  let a = (alice_sm) in
  let b = (bob_sm) in
  (((run_two_sm : $ two_sm [] []) a) b)
  :
  (Public * Public) -> Public
  by {
    unfold sideConditions
    unfold interpSideConditions
    simp
    split_grind
  }

def value :=
  OwlTy {
    (Data ⟨⊥⟩)
  }

def party_type :=
  OwlTy {
    ((Public -> ((unit -> unit) -> unit)) -> ((Public -> unit) -> unit) -> unit)
  }

#tc_with run_protocol_tc_inlined := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aKH <: Data lKH, aKL <: Data lKL ; · ;
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL]),
  msg  => Data lM
  ⊢
  let party1 : ($ party_type [] []) =
   (λ send =>
      λ recv =>
        let enc_high = π1 (π2 encH) in
        let enc_low  = π1 (π2 encL) in
        let key_high = π1 encH in
        let key_low  = π1 encL in
        let ciphertext1 = (corr_case lKH in (enc_high ⟨key_high, key_low⟩)) in
        let ciphertext2 = (corr_case lKL in (enc_low ⟨key_low, msg⟩)) in
        (send ciphertext1) (λ (_ : unit) : unit =>
          (send ciphertext2) (λ (_ : unit) : unit => ()))) in


  let party2 : ($ party_type [] []) =
  (λ send =>
    λ recv =>
      let dec_high  = π2 (π2 encH) in
      let dec_low   = π2 (π2 encL) in
      let key_high  = π1 encH in
      recv (λ (c1 : Public) : unit =>
        corr_case lKH in
        case (dec_high ⟨key_high, c1⟩) with
        | inl key_low' =>
            recv (λ (c2 : Public) : unit =>
              corr_case lKL in
              case (dec_low ⟨key_low', c2⟩) with
              | inl _ => (send "0") (λ (_ : unit) : unit => ())
              | inr _ => (send "1") (λ (_ : unit) : unit => ()))
        | inr _ =>
            (send "1") (λ (_ : unit) : unit => ()))) in


  -- run protocol
  λ (_ : unit) : (Public * Public) -> Public =>
      let k1 : (Ref (Public -> unit))   = alloc (λ (_ : Public) : unit => ()) in
      let k2 : (Ref (Public -> unit))   = alloc (λ (_ : Public) : unit => ()) in
      let out1 : (Ref Public) = alloc ("" : Public) in
      let out2 : (Ref Public) = alloc ("" : Public) in
      let send1 : (Public -> ((unit -> unit) -> unit)) = (λ (v : Public) : ((unit -> unit) -> unit) =>
       λ (k : (unit -> unit)) : unit =>
         (out1 := v) ;
         (k1 := (λ (_ : Public) : unit => k ()))) in
      let recv1 : (Public -> unit) -> unit = (λ (k : (Public -> unit)) : unit =>
         (k1 := k)) in
      let send2 : (Public -> (unit -> unit) -> unit) = (λ (v : Public) : ((unit -> unit) -> unit) =>
        λ (k : (unit -> unit)) : unit =>
          (out2 := v) ;
          (k2 := (λ (_ : Public) : unit => k ()))) in
       let recv2 : (Public -> unit) -> unit = (λ (k : (Public -> unit)) : unit =>
        (k2 := k)) in
    ((party1 send1) recv1) ;
    ((party2 send2) recv2) ;
    (λ (args : (Public * Public)) : Public =>
      let (b, v) = args in
        if b then
          let _  = ((!k1) v) in
          !out1
        else
          let _ = ((!k2) v) in
          !out2)
  :
  unit -> ((Public * Public) -> Public)
  by {
    unfold sideConditions
    simp
    try split_grind
  }

#tc_with run_protocol_client_server := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aPSK <: Data lKH, aKX <: Data lKL, aX <: Data lM ; · ;
  encPSK => ($ ENC_Inner [lKH] [aKX, aPSK]),
  encKX => ($ ENC_Inner [lKL] [Data lM, aKX]) ,
  x => Data lM
  ⊢
  let server : ($ party_type [] []) =
    λ send =>
    λ recv =>
      let enc_psk = π1 (π2 encPSK) in
      let psk     = π1 encPSK       in
      let dec_kx  = π2 (π2 encKX)  in
      let key_x   = π1 encKX        in
      let ct1 = corr_case lKH in (enc_psk ⟨psk, key_x⟩) in
      (send ct1) (λ (_ : unit) : unit =>
        recv (λ (ct2 : Public) : unit =>
          corr_case lKL in
          case (dec_kx ⟨key_x, ct2⟩) with
          | inl _ => ()
          | inr _ => ())) in


  let client : ($ party_type [] []) =
    λ send =>
    λ recv =>
      let dec_psk = π2 (π2 encPSK) in
      let enc_kx  = π1 (π2 encKX)  in
      let psk     = π1 encPSK       in

      recv (λ (ct1 : Public) : unit =>
        corr_case lKH in
        case (dec_psk ⟨psk, ct1⟩) with
        | inl key_x' =>
            let ct2 = corr_case lKL in (enc_kx ⟨key_x', x⟩) in
            (send ct2) (λ (_ : unit) : unit => ())
        | inr _ => ()) in


  -- run protocol
  λ (_ : unit) : (Public * Public) -> Public =>
    let s2c_k   : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
    let s2c_out : (Ref Public)           = alloc ("" : Public) in
    let c2s_k   : (Ref (Public -> unit)) = alloc (λ (_ : Public) : unit => ()) in
    let c2s_out : (Ref Public)           = alloc ("" : Public) in

    let send_server : (Public -> (unit -> unit) -> unit) =
      λ (v : Public) : ((unit -> unit) -> unit) =>
      λ (k : (unit -> unit)) : unit =>
        (s2c_out := v) ;
        (s2c_k   := (λ (_ : Public) : unit => k ())) in

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
        (c2s_k   := (λ (_ : Public) : unit => k ())) in

    ((server send_server) recv_server) ;

    ((!s2c_k) (!s2c_out)) ;

    ((!c2s_k) (!c2s_out)) ;

    (λ (args : (Public * Public)) : Public =>
      let (b, v) = args in
        if b then
          let _ = ((!s2c_k) v) in !s2c_out
        else
          let _ = ((!c2s_k) v) in !c2s_out)
  :
  unit -> ((Public * Public) -> Public)
  by {
    unfold sideConditions
    simp
    try split_grind
  }
/-

#tc protocol := lM, lKL ⊐ lM, lKH ⊐ lKL; · ; aKH <: Data lKH, aKL <: Data lKL ;
  --  Make it : instead of =>
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL] ),
  msg => Data lM,
  io => Public -> Public
 ⊢
  let key_low = π1 encL in
  let enc_low = π1 (π2 encL) in
  let dec_low = π2 (π2 encL) in

  let key_high = π1 encH in
  let enc_high = π1 (π2 encH) in
  let dec_high = π2 (π2 encH) in

  -- Alice's code
  let ctxt1 = (corr_case lKH in ( enc_high ⟨ key_high, key_low⟩ ))  in
  let ctxt2 = (corr_case lKL in ( enc_low ⟨ key_low, msg ⟩ )) in
  -- TODO: Ask Michael about parsing this better vvv
  let unused = io ctxt1  in -- Should be "let _ "
  let unused = io ctxt2  in

  -- Alice's state = whether or not she's been run
  -- Query Alice, if true, do things, else nothing
  -- 3 states : 1. do nothing 2. output ciphertexts 3. ciphertexts

  -- Bob's code (similar):
  -- Initial State
  -- Supply First CipherText -> First Decryption State
  -- Supply Second CipherText -> Second Decryption State
  -- Final State -> State
  -- Output to the network via the state machine "0" or "1"

  -- Alice in detail
  -- Initial State1
  -- (_, State1) -> (CipherText1, State2)
  -- (_, State2) -> (CipherText2, Done)
  -- (_, Done) -> ("", Done)

  -- Bob in detail
  -- Initial State1
  -- (CipherText1 -> (0, State2)) -- Store key when entering State2 (key type is aKL if lKH is NOT corrupt, using corr ?)
  --                                                                (key type is Public if lKH is corrupt)
  -- (CipherText1 -> (1, Done))
  -- (CipherText2 -> (0/1, Done)) -- make sure to grab key from memory
  -- (_, Done) -> ("", Done)

  -- Bob's code
  corr_case lKH in
  -- For the binary: 0x1234. Represent this as a list of U8s.
  case dec_high ⟨key_high, io ""⟩ in -- Case "with"
  | inl key_low' =>
    corr_case lKL in
    case dec_low ⟨key_low', io ""⟩ in
    | inl success => () -- Use () instead of *
    | inr _fail => ()
  --  Make "_" work as an identifier
  | inr _fail => ()
  :
    unit

  /-
    Unit -> (
      (Public -> Public) // Oracle for the adversary to call alice
      *
      (Public -> Public) // oracle for the adversary to call bob
    )
  -/
by {
    unfold sideConditions
    simp
    grind
}

-/
