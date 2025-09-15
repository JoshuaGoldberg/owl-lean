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
| Add : Expr Γ -> Expr Γ -> Expr Γ

inductive Ty : Type
| bool : Ty
| int : Ty

def TyEnv (n : Nat) := Fin n → Ty

def cons (x : X) (f : Fin n -> X) (m : Fin (n + 1)) : X :=
  match m with
  | ⟨0,_⟩ => x
  | ⟨k+1, hk⟩ =>
      have hk' : k < n := Nat.lt_of_succ_lt_succ hk
      let i : Fin n := ⟨k, hk'⟩
      (f i)

inductive has_type : TyEnv Γ -> Expr Γ -> Ty -> Prop where
| T_True {Γ} : has_type Γ .True .bool
| T_False : has_type Γ .False .bool
| T_NatLit : has_type Γ (.NatLit n) .int
| T_Ident : has_type Γ (.Ident i) (Γ i)
| T_Ite : has_type Γ g .bool ->
          has_type Γ thn t ->
          has_type Γ els t ->
          has_type Γ (.Ite g thn els) t
| T_Bind : has_type Γ e1 τ1 ->
           has_type (cons τ1 Γ) e2 τ2 ->
           has_type Γ (.Bind e1 e2) τ2
| T_Add : has_type Γ e1 .int ->
          has_type Γ e2 .int ->
          has_type Γ (.Add e1 e2) .int

syntax "tc" : tactic

macro_rules
  | `(tactic| tc) =>
  `(tactic|
    first
    | apply has_type.T_True
    | apply has_type.T_False
    | apply has_type.T_NatLit
    | apply has_type.T_Ident
    | (apply has_type.T_Ite; tc; tc; tc)
    | (apply has_type.T_Bind; tc; tc)
    | (apply has_type.T_Add; tc; tc)
  )

-- empty gamma
def empty_gamma : TyEnv 0 := fun i => nomatch i

-- example : True has type bool
example : has_type empty_gamma Expr.True Ty.bool := by
  tc

example : has_type empty_gamma (Expr.Add (Expr.NatLit 1) (Expr.NatLit 2)) Ty.int := by
  tc

-- example : let x = 5 in x + 3
example : has_type empty_gamma
  (Expr.Bind (Expr.NatLit 5) (Expr.Add (Expr.Ident 0) (Expr.NatLit 3))) Ty.int := by
    tc

-- a TinyPPL parser and elaborator
open Lean Elab Meta
declare_syntax_cat tiny_lang
syntax num : tiny_lang
syntax tiny_lang "←" tiny_lang ";" tiny_lang : tiny_lang
syntax ident : tiny_lang
syntax "true" : tiny_lang
syntax "false" : tiny_lang
syntax "if" tiny_lang "then" tiny_lang "else" tiny_lang : tiny_lang
syntax "(" tiny_lang ")" : tiny_lang
syntax tiny_lang "+" tiny_lang : tiny_lang

inductive SExpr : Type
| True : SExpr
| False : SExpr
| NatLit : (n : Nat) → SExpr
| Ident : String → SExpr
| Ite : (g : SExpr) → (thn : SExpr) → (els : SExpr) → SExpr
| Bind : String -> (e1 : SExpr) → (e2 : SExpr) → SExpr
| Add : SExpr -> SExpr -> SExpr

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
  | `(tiny_lang| $n:num) =>
    mkAppM ``SExpr.NatLit #[mkNatLit n.getNat]
  | `(tiny_lang| $e1:tiny_lang + $e2:tiny_lang) => do
    let elab_e1 ← elabTinylang e1
    let elab_e2 ← elabTinylang e2
    mkAppM ``SExpr.Add #[elab_e1, elab_e2]
  | _ => throwUnsupportedSyntax

-- TODO 1: Finish and connect to above elaborator
-- TODO 2: Extend to Owl language
def SExpr.elab (s : SExpr) (c : TCtx) : Option (Expr c.length) :=
  match s with
  | .Ident i =>
    match TCtx.lookup c i with
    | .none => .none
    | .some j => .some (Expr.Ident j)
  | .Bind s e1 e2 =>
      match (SExpr.elab e1 c) with
      | .none => .none
      | .some e1' =>
        match (SExpr.elab e2 (s::c)) with
        | .none => .none
        | .some e2' => .some (Expr.Bind e1' e2')
  | .True => .some (Expr.True)
  | .False => .some (Expr.False)
  | .Ite g thn els =>
    match (SExpr.elab g c) with
    | .none => .none
    | .some g' =>
      match (SExpr.elab thn c) with
      | .none => .none
      | .some thn' =>
        match (SExpr.elab els c) with
        | .none => .none
        | .some els' => .some (Expr.Ite g' thn' els')
  | .Add e1 e2 =>
    match (SExpr.elab e1 c) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 c) with
      | .none => .none
      | .some e2' => .some (Expr.Add e1' e2')
  | .NatLit n => .some (Expr.NatLit n)

def elabHelper (s : SExpr) : Expr 0 :=
  match SExpr.elab s [] with
  | .some e => e
  | .none => Expr.False --dummy value

elab "tinylang" "{" p:tiny_lang "}" : term => do
  let sexprTerm : Expr <- elabTinylang p
  let sVal : SExpr <-
    (unsafe do
      Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm)
  match SExpr.elab sVal [] with
  | .none =>
      throwError "tinylang: ill-formed term"
  | .some _ => mkAppM ``elabHelper #[sexprTerm]

#eval tinylang {
  x ← true;
  y ← false;
  if y then x else (2 + y)
}

#eval tinylang {
  x ← 1;
  y ← true;
  z ← 2;
  if y then (y + z) else (x + y)
}

def foo := tinylang {
  x ← 1;
  z ← 2;
  (if true then x else z)
}

theorem foo_ok : has_type empty_gamma foo .int := by
  tc
