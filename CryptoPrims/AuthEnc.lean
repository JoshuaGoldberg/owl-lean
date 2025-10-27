import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping
open Lean PrettyPrinter Delaborator SubExpr

set_option maxHeartbeats 1000000

def genKey : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def enc : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def dec : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def rand : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def eq : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def ENC :=
  OwlTy [lK, lM] [tau] {
    (∃ alphaK <: (Data lK) .
                  (alphaK *
                   ((corr (lK) ? ((Public * Public) -> Public) : ((alphaK * tau) -> Public)) *
                    (corr (lK) ? ((Public * Public) -> Public) : ((alphaK * Public) -> (tau + Unit))))))
  }

def EncIdeal :=
  Owl [lK, lM] [tau] [] {
    let k = (⟨genKey⟩ (["0"], ["0"]) : Data lK) in
    let L = alloc (λ (null : Public) : (tau + Unit) => ı2 *) in
    let enc' = (if corr (lK) then
                  (λ (x : Public * Public) : Public => ⟨enc⟩ (π1 x, π2 x))
                else
                  λ (x : (Data lK * tau)) : Public =>
                    let c = ⟨rand⟩ (zero ((π2 x) : Data lM), ["0"]) in
                    let L_old = (! L) in
                    let u = L := (λ (y : Public) : (tau + Unit) =>
                        if ⟨eq⟩(y, c) then ı1 (π2 x) else L_old [y])
                    in
                    c)
    in
    let dec' = (if corr (lK) then
                  λ (x : Public * Public) : Public => ⟨dec⟩ (π1 x, π2 x)
                else
                  λ (x : (Data lK * Public)) : (tau + Unit) => (!L) [π2 x])
    in
    pack (Data lK, ⟨k, ⟨(enc'), (dec')⟩⟩)
  }

theorem EncIdeal.wf :
  ( ( lK, lM ⊏ lK );
  · ;
  ( tau <: Data lM );
  · ;
   ($ EncIdeal [lK, lM] [tau] []) ⊢ ($ ENC [lK, lM] [tau])) := by
    tc_man (
      try simp
      try auto_solve_fast

    )
