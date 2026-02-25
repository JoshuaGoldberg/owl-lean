import Lean
import OwlLean.TypeChecker.OwlComplete

open Lean Meta Elab Tactic

open OwlTc

attribute [simp] Fin.foldr_succ

#tc example0 :=  · ; · ; · ; · ⊢
  λ (x : Public) : Public => "0" : (Public -> Public)  by {
      unfold sideConditions
      simp
  }

#tc ENC_FUNC := · ; · ; · ; · ⊢
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ ("0", "0") : Data betaK) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 ()) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau)) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), "0") in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old y))) in
                    c))
    in
    let dec' : corr (betaK) ? (Public * Public) -> Public : (Data betaK * Public) -> (tau + unit) = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + unit) => (!L) π2 x))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), dec'⟩⟩)
    :
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
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
def ENC_Inner := OwlTy [lK] [tM, tK] {
    ( tK *
        ((corr (lK) ? (Public * Public) -> Public : (tK * tM) -> Public) *
        (corr (lK) ? (Public * Public) -> (Public + unit) : (tK * Public) -> (tM + unit))))
}

def ENC := OwlTy [ lK ] [ tM ] {
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
def StateMachine := OwlTy [] [] {
  ∃ S <: Any . (S * ((S * Public) -> (S * Public)))
}

-- state machine execution type
def run_sm_ty := OwlTy [] [] {
  $ StateMachine [] [] -> (Public -> Public)
}

-- actual code for the state machine
def run_sm_tm := Owl [] [] [] {
  λ (m : $ StateMachine [] []) : (Public -> Public) =>
  unpack m as (S, contents) in
  let state_ref = alloc (π1 contents) in
  let step = π2 contents in
  λ (input: Public) : Public =>
    let result = step ⟨!state_ref, input⟩ in
    let _unused = (state_ref := π1 result) in
    π2 result
}

def two_sm := OwlTy [] [] {
  $ StateMachine [] [] -> $ StateMachine [] [] -> ((Public * Public) -> Public)
}

def run_two_tm := Owl [] [] [] {
  λ (a : $ StateMachine [] []) : ($ StateMachine [] [] -> (Public * Public) -> Public) =>
  λ (b : $ StateMachine [] []) : ((Public * Public) -> Public) =>
  -- generate a single state machine run function
  let A = $ run_sm_tm [] [] [] a in
  -- let's do it again!
  let B = $ run_sm_tm [] [] [] b in
  λ (val : (Public * Public)) : Public =>
    let (det, msg) = val in
    if (⟨"eq"⟩ (det, "0")) then
      A msg
    else
      B msg
}

-- assume eq is a default function
def alice_sm := Owl [lKL, lKH] [] [encH, encL, msg] {
  (pack (Public,
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
  : $ StateMachine [] [])
}

def bob_sm := Owl [lKL, lKH] [] [encH, encL] {
  (pack (Public,
    ⟨"0",
      (λ (args : (Public * Public)) : (Public * Public) =>
        let dec_high = π2 (π2 encH) in
        let dec_low = π2 (π2 encL) in
        let key_high = π1 encH in
        let key_store = alloc (π1 encL) in
        let (state, input) = args in
        if (⟨"eq"⟩ (state, "0")) then
          corr_case lKH in
          case (dec_high ⟨key_high, input⟩) in
          | inl key_low' =>
              let _u = (key_store := key_low') in
              ⟨"1", "0"⟩
          | inr _fail =>
              ⟨"10", "1"⟩
        else if (⟨"eq"⟩ (state, "1")) then
          let stored_key = (!key_store) in
          corr_case lKL in
          case (dec_low ⟨stored_key, input⟩) in
          | inl _success =>
              ⟨"10", "0"⟩
          | inr _fail =>
              ⟨"10", "1"⟩
        else
          ⟨"10", ""⟩)
    ⟩)
  : $ StateMachine [] [])
}

def run_alice_bob :=
 Owl [lKL, lKH] [] [encH, encL, msg] {
  let a = ($ alice_sm [lKL, lKH] [] [encH, encL, msg]) in
  let b = ($ bob_sm [lKL, lKH] [] [encH, encL]) in
  ((($ run_two_tm [] [] [] : $ two_sm [] []) a) b)
 }

-- typecheck (nice!)
#tc run_sm_tc := · ; · ; · ; ·
  ⊢
  $ run_sm_tm [] [] []
  :
  $ run_sm_ty [] []
  by {
    unfold sideConditions
    simp
    try grind
  }

-- typecheck 2 (nice!)
#tc run_two_sm_tc := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; · ; ·
  ⊢
  $ run_two_tm [] [] []
  :
  $ two_sm [] []
  by {
    unfold sideConditions
    simp
    try grind
  }

#tc alice_tc := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aKH <: Data lKH, aKL <: Data lKL ;
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL]),
  msg => Data lM
  ⊢
  $ alice_sm [lKL, lKH] [] [encH, encL, msg]
  :
  $ StateMachine [] []
  by {
    unfold sideConditions
    simp
    grind
  }

#tc bob_tc := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aKH <: Data lKH, aKL <: Data lKL ;
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL])
  ⊢
  $ bob_sm [lKL, lKH] [] [encH, encL]
  :
  $ StateMachine [] []
  by {
    unfold sideConditions
    simp
    grind
  }

-- the whole double state machine
#tc tc_run_alice_bob := lM, lKL ⊐ lM, lKH ⊐ lKL ; · ; aKH <: Data lKH, aKL <: Data lKL ;
  encH => ($ ENC_Inner [lKH] [aKL, aKH]),
  encL => ($ ENC_Inner [lKL] [Data lM, aKL]),
  msg => Data lM
  ⊢
  ($ run_alice_bob [lKL, lKH] [] [encH, encL, msg])
  :
  (Public * Public) -> Public
  by {
    unfold sideConditions
    simp
    split_grind
  }

def value :=
  OwlTy [] [] {
    (Data ⟨Owl.L.bot⟩)
  }

-- trivial binary values
def party1 :=
  Owl [] [] [send, recv] {
    send "10101" (λ (_x : unit) : unit => send "1010" (λ (_y : unit) : unit => ()))
  }

-- trivial binary value
def do_some_stuff :=
  Owl [] [] [c1, c2] {
    "1111011"
  }

def party2 :=
  Owl [] [] [send, recv] {
    recv (λ c1 =>
      recv (λ c2 =>
        if (⟨"eq"⟩ ($ do_some_stuff [] [] [c1, c2], "1111011")) then
          send (⟨"^"⟩(c1, c2)) (λ _x => ())
        else ()))
  }

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




/-

-- "[0]" represents garbage values not needed for computation
theorem enc_i :
  ( · ; · ; · ; · ⊢
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    let L = alloc (λ (null : Public) : (tau + Unit) => ı2 *) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau)) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), ["0"]) in
                    let L_old = (! L) in
                    let sc = L := (λ (y : Public) : (tau + Unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else L_old [y]) in
                    c))
    in
    let dec' = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + Unit) => (!L) [π2 x]))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), (corr_case betaK in dec')⟩⟩)
    :
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))).ok :=
    by
      simp
      whnf
      simp
      done

















      -- Public -> (x + Unit)
      -- x + Unit












/-

open EStateM

theorem enc_ty2 :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ⊢
      pack (Unit, *)
      :
      (∃ alphaK <: Unit . alphaK)) :=
    by
      apply OwlTc.infer_sound
      dsimp [OwlTc.infer, OwlTc.check_subtype, OwlTc.has_type_infer]
      simp [EStateM.run]
      simp [pure, EStateM.pure]





theorem test_let_2 :
  ( · ; · ; · ; · ⊢
      let (x, y) = ⟨* , ["0"]⟩ in
      y
      :
      Public) :=
    by
      apply infer_sound
      simp
      dsimp [infer]
      dsimp [check_subtype]
      simp

theorem test_let_3 :
  ( · ; · ; · ; · ⊢
      let (x, y, z) = ⟨⟨* , *⟩ , ⟨*, ["0"]⟩⟩ in
      z
      :
      Public) :=
    by
    tc_man (
      try simp
      try auto_solve
    )

theorem enc_ty_contra :
  ((betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      (if corr (betaK) then ((λ x => *) : Public -> Unit) else ((λ x => x) : Data betaC -> Data betaC))
      :
      (Public -> Unit)) :=
    by
    tc_man (
      try simp
      auto_solve
    )

theorem enc_length_test :
  ( (betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ a => λ x => λ x => λ b =>
      λ x => λ x => λ y => λ x => λ h => λ x => λ a => λ x => λ x => λ x => λ x => λ x => λ x => λ x =>
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ z => λ x => λ x => λ x => λ x => λ x => ⟨a, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨z, x⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      :
      (Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->

       ((Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * Public))))))))))))) :=
    by
    tc_man (
      try simp
      auto_solve
    )


theorem enc_r :
  ( (betaK, betaM) ; (corr(betaK)) ; (tau <: Data betaM) ; · ⊢
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    pack (Data betaK, ⟨k, ⟨λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x),
                           λ (y : (Public * Public)) : Public => ⟨"dec"⟩ (π1 y, π2 y)⟩⟩)
    :
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * (Data betaM)) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
      simp
      apply infer_sound
      dsimp [infer]
      dsimp [check_subtype]


theorem enc_unpack :
  ( (betaK, betaM ⊑ betaK) ; · ; (tau <: Data betaM) ;
  (E => (∃ alphaK <: (Data betaK) . (alphaK *
                                     ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                      (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit))))),
   x => tau) ⊢
    (corr_case betaK in
     unpack E as (alpha, ked) in
     (π1 (π2 ked)) [⟨(π1 ked), x⟩])
    :
    Public) :=
    by
    tc_man (
      try simp
      auto_solve
    )

-/

abbrev mySeq := ( (l1, l2 ⊒ l1, l3 ⊒ l2) ; · ; (a <: Data l2, b <: Data l1) ;
  (E1 => (∃ alphaK <: (Data l3) .
                        (alphaK *
                         ((corr (l3) ? (Public * Public) -> Public : (alphaK * (Data l2)) -> Public) *
                          (corr (l3) ? (Public * Public) -> Public : (alphaK * Public) -> (a + Unit))))),
   E2 => (∃ alphaK <: (Data l2) .
                        (alphaK *
                         ((corr (l2) ? (Public * Public) -> Public : (alphaK * (Data l1)) -> Public) *
                          (corr (l2) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ⊢
    (corr_case l3 in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       (π1 (π2 ked1)) [⟨(π1 ked1), (π1 ked2)⟩])
    :
    Public)




theorem enc_layered :
  mySeq.ok :=  by
    whnf
    simp
    grind

-/
