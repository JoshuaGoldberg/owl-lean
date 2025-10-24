import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping
open Lean PrettyPrinter Delaborator SubExpr

set_option maxHeartbeats 1000000

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
