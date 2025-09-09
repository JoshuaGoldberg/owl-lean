import OwlLean.OwlLang.Owl
open Owl

-- sanity checks
#check (tm.error : tm 0 0 0)
#check (ty.Any : ty 0 0)

inductive SBinary : Type
| bzero : SBinary -> SBinary
| bone : SBinary -> SBinary
| bend : SBinary

inductive SLabel : Type
| var_label : String -> SLabel
| latl : String -> SLabel
| ljoin : SLabel -> SLabel -> SLabel
| lmeet : SLabel -> SLabel -> SLabel

inductive SCondSym : Type
| leq : SCondSym
| geq : SCondSym
| gt : SCondSym
| lt : SCondSym
| nleq : SCondSym
| ngeq : SCondSym
| ngt : SCondSym
| nlt : SCondSym

inductive SConstr : Type where
| condition : SCondSym -> SLabel -> SLabel -> SConstr

inductive STy : Type where
| var_ty :String -> STy
| Any : STy
| Unit : STy
| Data : SLabel -> STy
| Ref : STy -> STy
| arr : STy -> STy -> STy
| prod : STy -> STy -> STy
| sum : STy -> STy -> STy
| all : STy -> STy -> STy
| ex : String -> STy -> STy -> STy
| all_l : String -> SCondSym -> SLabel -> STy -> STy
| t_if : SConstr -> STy -> STy -> STy

inductive SExpr : Type where
| var_tm : String -> SExpr
| error : SExpr
| skip : SExpr
| bitstring : SBinary -> SExpr
| loc : Nat -> SExpr
| fixlam : String -> String -> SExpr -> SExpr
| tlam : SExpr -> SExpr
| l_lam : String -> SExpr -> SExpr
| Op : op -> SExpr -> SExpr -> SExpr
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
| tapp : SExpr -> SExpr
| lapp : SExpr -> SLabel -> SExpr
| pack : SExpr -> SExpr
| unpack : SExpr -> String -> SExpr -> SExpr
| if_tm :
    SExpr -> SExpr -> SExpr -> SExpr
| if_c :
    SConstr -> SExpr -> SExpr -> SExpr
| sync : SExpr -> SExpr

open Lean Elab Meta

declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_binary
declare_syntax_cat owl_constr
declare_syntax_cat owl_cond_sym

syntax ident : owl_label
syntax term : owl_label
syntax "⟨" owl_label "⟩"  : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "(" owl_label ")" : owl_label

syntax "(" owl_constr ")" : owl_constr
syntax owl_label owl_cond_sym owl_label : owl_constr

syntax "⊑" : owl_cond_sym
syntax "⊒" : owl_cond_sym
syntax "⊏" : owl_cond_sym
syntax "⊐" : owl_cond_sym
syntax "̸⊑" : owl_cond_sym
syntax "̸⊒" : owl_cond_sym
syntax "̸⊏" : owl_cond_sym
syntax "̸⊐" : owl_cond_sym

syntax num : owl_binary

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
