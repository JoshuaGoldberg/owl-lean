import Lean

open Lean Elab Meta Tactic Command

def foo := (· + 2)

def complexExpr : Nat := 500 * 500 * 500 * 500


structure Foo {α : Type} (y : α) : Type where
  x : α
  pf : x = y

def mkFoo (e : α) : Foo e :=
  ⟨e, by rfl⟩


def tst : Command.CommandElabM Unit := do
  elabCommand (<- `(command| def $(mkIdent `abcd) := mkFoo $(mkIdent `complexExpr)))

elab "mycommand" : command => do
  tst

mycommand


#check abcd

#eval abcd.x
