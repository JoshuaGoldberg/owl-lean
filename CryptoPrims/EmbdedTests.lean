import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping
open Lean PrettyPrinter Delaborator SubExpr

set_option maxHeartbeats 1000000

-- non functional
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

-- non functional
def genSk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def pk_of_sk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def vk_of_sk : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def and_op : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def combine : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def sign : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def vrfy : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def test_label :=
  OwlLabel [x, y, z] {
    x
  }

theorem label_test_ty :
  ((lx, ly) ; · ; · ; · ;
      ["0"]
      ⊢
      Data ($ test_label [⟨Owl.L.bot⟩, lx, ly])) :=
    by
    tc_man (
      try simp
      try auto_solve
    )


def ENC :=
  OwlTy [L1, L2] [tau] {
    (∃ alphaK <: (Data L1) .
                  (alphaK *
                   ((corr (L1) ? (Public * Public) -> Public : (alphaK * (Data L2)) -> Public) *
                    (corr (L1) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))
  }

theorem enc_layered2_high_low :
  ( (L_sec, L_low ⊒ L_sec, L_high ⊒ L_low) ; · ; (a <: Data L_sec, b <: Data L_low) ;
  (E1 => ($ ENC [L_sec, L_low] [a]),
   E2 => (∃ alphaK <: (Data L_high) .
                        (alphaK *
                         ((corr (L_high) ? (Public * Public) -> Public : (alphaK * (Data L_low)) -> Public) *
                          (corr (L_high) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ;
    (corr_case L_low in
      (corr_case L_high in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       ((λ x =>
        let c1 = ((π1 (π2 ked1)) [⟨(π1 ked1), x⟩] : Public) in
        let c2 = ((π1 (π2 ked2)) [⟨(π1 ked2), (π1 ked1)⟩] : Public) in
        ⟨combine⟩(c1, c2)) : ((Data L_sec) -> Public))))
    ⊢
    ((Data L_sec) -> Public)) :=
    by
    tc_man (
      try simp
      auto_solve_fast
    )
