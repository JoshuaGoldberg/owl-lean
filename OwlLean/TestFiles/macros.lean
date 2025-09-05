--- Version 2.0 of TinyPPL
--- This version is implicitly typed so that the interpreter is total.

import Lean
import Std.Data.HashMap
-- a proba

inductive Expr : Nat → Type
| True : Expr Γ
| False : Expr Γ
| NatLit : (n : Nat) → Expr Γ
| Ident {Γ} : (i : Fin Γ) → Expr Γ
| Ite : (g : Expr Γ) → (thn : Expr Γ) → (els : Expr Γ) → Expr Γ
| Bind : (e1 : Expr Γ) → (e2 : Expr (Γ + 1)) → Expr Γ


-- a TinyPPL parser and elaborator
open Lean Elab Meta
declare_syntax_cat tiny_lang
syntax Parser.numLit : tiny_lang
syntax tiny_lang "←" tiny_lang ";" tiny_lang : tiny_lang
syntax ident : tiny_lang
syntax "true" : tiny_lang
syntax "false" : tiny_lang
syntax "if" tiny_lang "then" tiny_lang "else" tiny_lang : tiny_lang
syntax "(" tiny_lang ")" : tiny_lang


inductive SExpr : Type
| True : SExpr
| False : SExpr
| NatLit : (n : Nat) → SExpr
| Ident : String → SExpr
| Ite : (g : SExpr) → (thn : SExpr) → (els : SExpr) → SExpr
| Bind : String -> (e1 : SExpr) → (e2 : SExpr) → SExpr

def TCtx := List String

def TCtx.lookup (t : TCtx) (s : String) : Option (Fin t.length) :=
  match t with
  | [] => .none
  | x::xs =>
    if x == s then .some ⟨0, by simp [List.length]⟩ else
      match TCtx.lookup xs s with
      | .none => .none
      | .some i => .some ⟨1 + i, by
        simp [List.length]
        omega⟩

-- the throwError function is available inside the MetaM monad, which raises a user error
partial def elabTinylang : Syntax → MetaM Expr
  | `(tiny_lang| ( $e:tiny_lang )) => elabTinylang e
  | `(tiny_lang| true) => mkAppM ``SExpr.True  #[]
  | `(tiny_lang| false) => mkAppM ``SExpr.False  #[]
  | `(tiny_lang| $id:ident ← $e1:tiny_lang; $e2:tiny_lang) => do
    let elab_e1 ← elabTinylang e1
    let elab_e2 ← elabTinylang e2
    mkAppM ``SExpr.Bind #[mkStrLit id.getId.toString, elab_e1, elab_e2]
  | `(tiny_lang| if $g:tiny_lang then $thn:tiny_lang else $els:tiny_lang) => do
    let elab_g ← elabTinylang g
    let elab_thn ← elabTinylang thn
    let elab_els ← elabTinylang els
    mkAppM ``SExpr.Ite #[elab_g, elab_thn, elab_els]
  | `(tiny_lang| $id:ident) =>
    mkAppM ``SExpr.Ident #[mkStrLit id.getId.toString]
  | _ => throwUnsupportedSyntax

elab "tinylang" "{" p:tiny_lang "}" : term => elabTinylang p

#eval tinylang {
  x ← true;
  y ← false;
  y
}

-- TODO 1: Finish and connect to above elaborator
-- TODO 2: Extend to Owl language
def SExpr.elab (s : SExpr) (c : TCtx) : Option (Expr c.length) :=
  match s with
  | .Ident i =>
    match TCtx.lookup c i with
    | .none => .none
    | .some j => Expr.Ident j
  | .Bind s e1 e2 => .none
    -- add s to c in the front; elab e1 under c; elab e2 under s::c
  | .True => .some (Expr.True)
  | .False => .some (Expr.False)
  -- if/then/else is just recursive
  | _ => .none
