import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap

open Owl

inductive SBinary : Type
| bzero : SBinary -> SBinary
| bone : SBinary -> SBinary
| bend : SBinary
deriving Repr

inductive SLabel (L : Lattice) : Type
| var_label : String -> SLabel L
| latl : L.labels -> SLabel L
| ljoin : SLabel L-> SLabel L-> SLabel L
| lmeet : SLabel L-> SLabel L-> SLabel L
| embedlabel : Owl.label L 0 -> SLabel L
| default : SLabel L
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

inductive SConstr (L : Lattice) : Type where
| condition : SCondSym -> SLabel L-> SLabel L-> SConstr L
deriving Repr

inductive STy (L : Lattice) : Type where
| var_ty :String -> STy L
| Any : STy L
| Unit : STy L
| Data : SLabel L-> STy L
| Ref : STy L -> STy L
| arr : STy L -> STy L -> STy L
| prod : STy L -> STy L -> STy L
| sum : STy L -> STy L -> STy L
| all : String -> STy L -> STy L -> STy L
| ex : String -> STy L -> STy L -> STy L
| all_l : String -> SCondSym -> SLabel L-> STy L -> STy L
| t_if : SConstr L -> STy L -> STy L -> STy L
| embedty : Owl.ty L 0 0 -> STy L
| Public : STy L
| default : STy L
deriving Repr

inductive SExpr (L : Lattice) : Type where
| var_tm : String -> SExpr L
| error : SExpr L
| skip : SExpr L
| bitstring : SBinary -> SExpr L
| loc : Nat -> SExpr L
| fixlam : String -> String -> SExpr L -> SExpr L
| tlam : String -> SExpr L -> SExpr L
| l_lam : String -> SExpr L -> SExpr L
| Op : Owl.op -> SExpr L -> SExpr L -> SExpr L
| zero : SExpr L -> SExpr L
| app : SExpr L -> SExpr L -> SExpr L
| alloc : SExpr L -> SExpr L
| dealloc : SExpr L -> SExpr L
| assign : SExpr L -> SExpr L -> SExpr L
| tm_pair : SExpr L -> SExpr L -> SExpr L
| left_tm : SExpr L -> SExpr L
| right_tm : SExpr L -> SExpr L
| inl : SExpr L -> SExpr L
| inr : SExpr L -> SExpr L
| case : SExpr L -> String -> SExpr L -> String -> SExpr L -> SExpr L
| tapp : SExpr L -> STy L -> SExpr L
| lapp : SExpr L -> SLabel L-> SExpr L
| pack : STy L -> SExpr L -> SExpr L
| unpack : SExpr L -> String -> String -> SExpr L -> SExpr L
| if_tm :
    SExpr L -> SExpr L -> SExpr L -> SExpr L
| if_c :
    SConstr L -> SExpr L -> SExpr L -> SExpr L
| sync : SExpr L -> SExpr L
| embedtm : Owl.tm L 0 0 0 -> SExpr L
| annot : SExpr L -> STy L -> SExpr L
| default : SExpr L
deriving Repr
