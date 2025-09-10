import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap

open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

inductive SBinary : Type
| bzero : SBinary -> SBinary
| bone : SBinary -> SBinary
| bend : SBinary
deriving Repr

inductive SLabel : Type
| var_label : String -> SLabel
| latl : String -> SLabel
| ljoin : SLabel -> SLabel -> SLabel
| lmeet : SLabel -> SLabel -> SLabel
deriving Repr

inductive SCondSym : Type
| leq : SCondSym
| geq : SCondSym
| gt : SCondSym
| lt : SCondSym
| nleq : SCondSym
| ngeq : SCondSym
| ngt : SCondSym
| nlt : SCondSym
deriving Repr

inductive SConstr : Type where
| condition : SCondSym -> SLabel -> SLabel -> SConstr
deriving Repr

inductive STy : Type where
| var_ty :String -> STy
| Any : STy
| Unit : STy
| Data : SLabel -> STy
| Ref : STy -> STy
| arr : STy -> STy -> STy
| prod : STy -> STy -> STy
| sum : STy -> STy -> STy
| all : String -> STy -> STy -> STy
| ex : String -> STy -> STy -> STy
| all_l : String -> SCondSym -> SLabel -> STy -> STy
| t_if : SConstr -> STy -> STy -> STy
deriving Repr

instance : Repr Owl.op where
  reprPrec _ _ := "<operation>"

inductive SExpr : Type where
| var_tm : String -> SExpr
| error : SExpr
| skip : SExpr
| bitstring : SBinary -> SExpr
| loc : Nat -> SExpr
| fixlam : String -> String -> SExpr -> SExpr
| tlam : String -> SExpr -> SExpr
| l_lam : String -> SExpr -> SExpr
| Op : Owl.op -> SExpr -> SExpr -> SExpr
| zero : SExpr -> SExpr
| app : SExpr -> SExpr -> SExpr
| alloc : SExpr -> SExpr
| dealloc : SExpr -> SExpr
| assign : SExpr -> SExpr -> SExpr
| tm_pair : SExpr -> SExpr -> SExpr
| left_tm : SExpr -> SExpr
| right_tm : SExpr -> SExpr
| inl : SExpr -> SExpr
| inr : SExpr -> SExpr
| case : SExpr -> String -> SExpr -> String -> SExpr -> SExpr
| tapp : SExpr -> STy -> SExpr
| lapp : SExpr -> SLabel -> SExpr
| pack : SExpr -> SExpr
| unpack : SExpr -> String -> SExpr -> SExpr
| if_tm :
    SExpr -> SExpr -> SExpr -> SExpr
| if_c :
    SConstr -> SExpr -> SExpr -> SExpr
| sync : SExpr -> SExpr
deriving Repr

open Lean Elab Meta

declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_binary
declare_syntax_cat owl_constr
declare_syntax_cat owl_cond_sym

-- syntax for labels
syntax ident : owl_label
syntax term : owl_label
syntax "⟨" owl_label "⟩"  : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "(" owl_label ")" : owl_label

partial def elabLabel : Syntax → MetaM Expr
  | `(owl_label| ( $e:owl_label)) => elabLabel e
  | `(owl_label| ⟨ $t:term ⟩ ) => do
      let t' ← Term.TermElabM.run' do
        Term.elabTerm t (mkConst ``Owl.Lcarrier)
      mkAppM ``SLabel.latl #[t']
  | `(owl_label| $e1:owl_label ⊔ $e2:owl_label) => do
      let elab_e1 <- elabLabel e1
      let elab_e2 <- elabLabel e2
      mkAppM ``SLabel.ljoin #[elab_e1, elab_e2]
  | `(owl_label| $e1:owl_label ⊓ $e2:owl_label) => do
      let elab_e1 <- elabLabel e1
      let elab_e2 <- elabLabel e2
      mkAppM ``SLabel.lmeet #[elab_e1, elab_e2]
  | `(owl_label| $id:ident) =>
    mkAppM ``SLabel.var_label #[mkStrLit id.getId.toString]
  | _ => throwUnsupportedSyntax

-- test parser for labels
elab "label_parse" "(" p:owl_label ")" : term =>
    elabLabel p

-- check that labels works
#eval label_parse(x ⊓ y)

-- syntax for cond symbols
syntax "⊑" : owl_cond_sym
syntax "⊒" : owl_cond_sym
syntax "⊏" : owl_cond_sym
syntax "⊐" : owl_cond_sym
syntax "!⊑" : owl_cond_sym
syntax "!⊒" : owl_cond_sym
syntax "!⊏" : owl_cond_sym
syntax "!⊐" : owl_cond_sym

partial def elabCondSym : Syntax → MetaM Expr
  | `(owl_cond_sym| ⊑) => mkAppM ``SCondSym.leq #[]
  | `(owl_cond_sym| ⊒) => mkAppM ``SCondSym.geq #[]
  | `(owl_cond_sym| ⊏) => mkAppM ``SCondSym.lt #[]
  | `(owl_cond_sym| ⊐) => mkAppM ``SCondSym.gt #[]
  | `(owl_cond_sym| !⊑) => mkAppM ``SCondSym.nleq #[]
  | `(owl_cond_sym| !⊒) => mkAppM ``SCondSym.ngeq #[]
  | `(owl_cond_sym| !⊏) => mkAppM ``SCondSym.nlt #[]
  | `(owl_cond_sym| !⊐) => mkAppM ``SCondSym.ngt #[]
  | _ => throwUnsupportedSyntax

-- test parser for cond_sym
elab "cond_sym_parse" "(" p:owl_cond_sym ")" : term =>
    elabCondSym p

-- check that cond_sym works
#eval cond_sym_parse(⊑)
#eval cond_sym_parse(!⊑)

-- syntax for contraints
syntax "(" owl_constr ")" : owl_constr
syntax owl_label owl_cond_sym owl_label : owl_constr

partial def elabConstr : Syntax → MetaM Expr
  | `(owl_constr| ( $e:owl_constr)) => elabConstr e
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let elab_l1 <- elabLabel l1
      let elab_l2 <- elabLabel l2
      let elab_c <- elabCondSym c
      mkAppM ``SConstr.condition #[elab_c, elab_l1, elab_l2]
  | _ => throwUnsupportedSyntax

-- test parser for constraints
elab "constraint_parse" "(" p:owl_constr ")" : term =>
    elabConstr p

-- check that constraints works
#eval constraint_parse(y ⊑ x)

-- syntax for binary
syntax str : owl_binary

partial def buildSBinaryExpr (chars : List Char) : MetaM Expr :=
  match chars with
  | [] => return mkConst ``SBinary.bend
  | '0' :: rest => do
    let restExpr <- buildSBinaryExpr rest
    mkAppM ``SBinary.bzero #[restExpr]
  | '1' :: rest => do
    let restExpr <- buildSBinaryExpr rest
    mkAppM ``SBinary.bone #[restExpr]
  | _ :: _ => throwError "Invalid binary character"

partial def elabBinary : Syntax → MetaM Expr
  | `(owl_binary| $val:str) => buildSBinaryExpr val.getString.data
  | _ => throwUnsupportedSyntax

-- test parser for binary
elab "binary_parse" "(" p:owl_binary ")" : term =>
    elabBinary p

-- check that binary works
#eval binary_parse("1101")

-- syntax for types
syntax "(" owl_type ")" : owl_type
syntax ident : owl_type
syntax "Any" : owl_type
syntax "Unit" : owl_type
syntax "Data" owl_label : owl_type
syntax "Ref" owl_type : owl_type
syntax owl_type "->" owl_type : owl_type
syntax owl_type "x" owl_type : owl_type
syntax owl_type "+" owl_type : owl_type
syntax "∀" owl_type "<:" owl_type "." owl_type : owl_type
syntax "∃" owl_type "<:" owl_type "." owl_type : owl_type
syntax "∀" owl_label owl_cond_sym owl_label "." owl_type : owl_type
syntax "if" owl_constr "then" owl_type "else" owl_type : owl_type

partial def elabType : Syntax → MetaM Expr
  | `(owl_type| ( $e:owl_type)) => elabType e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| Unit) => mkAppM ``STy.Unit #[]
  | `(owl_type| Data $l:owl_label) => do
    let elab_l <- elabLabel l
    mkAppM ``STy.Data #[elab_l]
  | `(owl_type| Ref $t:owl_type) => do
    let elab_t <- elabType t
    mkAppM ``STy.Ref #[elab_t]
  | `(owl_type| $t1:owl_type -> $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.arr #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type x $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.prod #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type + $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.sum #[elab_t1, elab_t2]
  | `(owl_type| ∀ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.all #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∃ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.ex #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∀ $id:ident $c:owl_cond_sym $l:owl_label . $t:owl_type) => do
    let elab_t <- elabType t
    let elab_l <- elabLabel l
    let elab_c <- elabCondSym c
    mkAppM ``STy.all_l #[mkStrLit id.getId.toString, elab_c, elab_l, elab_t]
  | `(owl_type| if $c:owl_constr then $t1:owl_type else $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    let elab_c <- elabConstr c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | _ => throwUnsupportedSyntax

-- test parser for types
elab "type_parse" "(" p:owl_type ")" : term =>
    elabType p

-- check that types works
#eval type_parse(Unit -> Unit)
#eval type_parse(∀ t <: Any . (t -> t))

-- syntax for terms
syntax "(" owl_tm ")" : owl_tm
syntax ident : owl_tm
syntax term : owl_tm
syntax "error" : owl_tm
syntax "*" : owl_tm
syntax "⌜" owl_binary "⌝" : owl_tm
syntax "fix" owl_tm "(" owl_tm ")" owl_tm : owl_tm
syntax "Λ." owl_tm : owl_tm
syntax "Λ" owl_tm "." owl_tm : owl_tm
syntax "⟨" owl_tm "," owl_tm "⟩" : owl_tm
syntax owl_tm "(" owl_tm owl_tm ")" : owl_tm
syntax "zero" owl_tm : owl_tm
syntax owl_tm owl_tm : owl_tm
syntax "alloc" owl_tm : owl_tm
syntax "!" owl_tm : owl_tm
syntax owl_tm ":=" owl_tm : owl_tm
syntax "π1" owl_tm : owl_tm
syntax "π2" owl_tm : owl_tm
syntax "ı1" owl_tm : owl_tm
syntax "ı2" owl_tm : owl_tm
syntax "case" owl_tm "in" owl_tm "=>" owl_tm "|" owl_tm "=>" owl_tm : owl_tm
syntax owl_tm "[]" : owl_tm
syntax owl_tm "[" owl_label "]" : owl_tm
syntax "pack" owl_tm : owl_tm
syntax "unpack" owl_tm "as" owl_tm "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" owl_cond_sym "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm

partial def elabTm : Syntax → MetaM Expr
  | `(owl_tm| ( $e:owl_tm)) => elabTm e
  | `(owl_tm| $id:ident) =>
        mkAppM ``SExpr.var_tm #[mkStrLit id.getId.toString]
  | _ => throwUnsupportedSyntax
