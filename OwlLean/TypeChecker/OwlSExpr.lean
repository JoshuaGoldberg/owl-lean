import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap

open Owl

inductive SBinary : Type
| bzero : SBinary -> SBinary
| bone : SBinary -> SBinary
| bend : SBinary
deriving Repr

inductive SLabel : Type
| var_label : String -> SLabel
| latl : Owl.Lcarrier -> SLabel
| ljoin : SLabel -> SLabel -> SLabel
| lmeet : SLabel -> SLabel -> SLabel
| embedlabel : Owl.label 0 -> SLabel
| default : SLabel
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
| embedty : Owl.ty 0 0 -> STy
| default : STy
deriving Repr

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
| pack : STy -> SExpr -> SExpr
| unpack : SExpr -> String -> String -> SExpr -> SExpr
| if_tm :
    SExpr -> SExpr -> SExpr -> SExpr
| if_c :
    SConstr -> SExpr -> SExpr -> SExpr
| sync : SExpr -> SExpr
| embedtm : Owl.tm 0 0 0 -> SExpr
| annot : SExpr -> STy -> SExpr
| default : SExpr
deriving Repr
