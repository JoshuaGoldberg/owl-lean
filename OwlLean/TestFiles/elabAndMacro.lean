import Lean
open Lean Elab Meta

-- simple lean macro and elab exercises

-- terms
macro "num1" : term => `(term| 42)

macro "add1" x:num : term => do
  `($x + 1)

macro_rules
| `(term| num2) => `(term| 7)
| `(num3) => `(200)
| `(term| add2 $x:num) => `(term| $x + 2)

elab "num4" : term => return mkNatLit 500

elab "add3" x:term : term => do
  let x ← Term.elabTerm x (mkConst ``Nat)
  mkAppM ``Nat.add #[x, mkNatLit 3]

elab_rules : term
| `(term| num5) => return mkNatLit 90
| `(term| add4 $x:term) => do
  let x ← Term.elabTerm x (mkConst ``Nat)
  mkAppM ``Nat.add #[x, mkNatLit 4]

-- proof it works
#eval (add1 7)
#eval num1
#eval num2
#eval num3
#eval (add2 5)

#eval num4
#eval (add3 7)
#eval num5
#eval (add4 10)

-- tactics
macro "my_simp" : tactic => `(tactic| simp)

macro "my_simp2" x:term : tactic => `(tactic| simp)

syntax "my_simp3" : tactic

syntax "my_simp4" num : tactic

macro_rules
| `(tactic| my_simp3) => `(tactic| simp)
| `(tactic| my_simp4 $x:num) => `(tactic| simp)

elab "my_simp5" : tactic => do
  let tac ← `(tactic| simp)
  Tactic.evalTactic tac

elab "my_simp6" x:num : tactic => do
  let tac ← `(tactic| simp)
  Tactic.evalTactic tac

syntax "my_simp7" : tactic
syntax "my_simp8" num : tactic
elab_rules : tactic
| `(tactic| my_simp7) => do
  let tac ← `(tactic| simp)
  Tactic.evalTactic tac
| `(tactic| my_simp8 $x:num) => do
  let tac ← `(tactic| simp)
  Tactic.evalTactic tac

-- proof it works
theorem ez : 1 = 1 := by
  my_simp

theorem ez2 : 2 = 2 := by
  my_simp2 2

theorem ez3 : 3 = 3 := by
  my_simp3

theorem ez4 : 4 = 4 := by
  my_simp4 4

theorem ez5 : 5 = 5 := by
  my_simp5

theorem ez6 : 6 = 6 := by
  my_simp6 6

theorem ez7 : 7 = 7 := by
  my_simp7

theorem ez8 : 8 = 8 := by
  my_simp8 8
