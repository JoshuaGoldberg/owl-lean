import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap

open Owl

inductive SLabel : Type
| var_label : String -> SLabel
| latl : Owl.Lcarrier -> SLabel
| ljoin : SLabel -> SLabel -> SLabel
| lmeet : SLabel -> SLabel -> SLabel
| embedlabel : Owl.label l -> List SLabel -> SLabel
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

inductive SRexp where
| var : String -> SRexp
| op : String -> SRexp -> SRexp -> SRexp
| const : String -> SRexp
deriving Repr

inductive STy : Type where
| var_ty : String -> STy
| Any : STy
| Unit : STy
| RData : SLabel -> SRexp -> STy
| Data : SLabel -> STy
| Ref : STy -> STy
| arr : STy -> STy -> STy
| prod : STy -> STy -> STy
| sum : STy -> STy -> STy
| all : String -> STy -> STy -> STy
| ex : String -> STy -> STy -> STy
| ex_r : String -> STy -> STy
| all_r : String -> STy -> STy
| all_l : String -> SCondSym -> SLabel -> STy -> STy
| t_if : SLabel -> STy -> STy -> STy
-- TODO: for the List Unit, make it a List RefinementExp
| embedty : Owl.ty l r d -> List SLabel -> List Unit -> List STy -> STy
| Public : STy
| default : STy
deriving Repr

mutual
    inductive SExpr : Type where
    | mk : Owl.opaqueSyntax -> SExprX -> SExpr
    deriving Repr


inductive SExprX : Type where
| var_tm : String -> SExprX
| error : SExprX
| skip : SExprX
| bitstring : String -> SExprX
| loc : Nat -> SExprX
| fixlam : String -> String -> SExpr -> SExprX
| elet : String -> SExpr -> SExpr -> SExprX
| tlam : String -> SExpr -> SExprX
| rlam : String -> SExpr -> SExprX
| l_lam : String -> SExpr -> SExprX
| Op : String -> SExpr -> SExpr -> SExprX
| zero : SExpr -> SExprX
| app : SExpr -> SExpr -> SExprX
| alloc : SExpr -> SExprX
| dealloc : SExpr -> SExprX
| assign : SExpr -> SExpr -> SExprX
| tm_pair : SExpr -> SExpr -> SExprX
| left_tm : SExpr -> SExprX
| right_tm : SExpr -> SExprX
| inl : SExpr -> SExprX
| inr : SExpr -> SExprX
| case : SExpr -> String -> SExpr -> String -> SExpr -> SExprX
| tapp : SExpr -> STy -> SExprX
| lapp : SExpr -> SLabel -> SExprX
| pack : STy -> SExpr -> SExprX
| unpack : SExpr -> String -> String -> SExpr -> SExprX
| if_tm :
    SExpr -> SExpr -> SExpr -> SExprX
| if_c :
    SLabel -> SExpr -> SExpr -> SExprX
| sync : SExpr -> SExprX
-- TODO: for the List Unit, make it a List RefinementExp
| embedtm : Owl.tm l r d m -> List SLabel -> List Unit -> List STy -> List SExpr -> SExprX
| annot : SExpr -> STy -> SExprX
| corr_case : SLabel -> SExpr -> SExprX
| default : SExprX
deriving Repr
end

inductive SPhiEntry : Type where
| PhiEntry : String -> SCondSym -> SLabel -> SPhiEntry
deriving Repr

inductive SPhi : Type where
| Phi_Cons : SPhiEntry -> SPhi -> SPhi
| Phi_End : SPhi
deriving Repr

inductive SDeltaEntry : Type where
| DeltaEntry : String -> STy -> SDeltaEntry
deriving Repr

inductive SDelta : Type where
| Delta_Cons : SDeltaEntry -> SDelta -> SDelta
| Delta_End : SDelta
deriving Repr

inductive SGammaEntry : Type where
| GammaEntry : String -> STy -> SGammaEntry
deriving Repr

inductive SGamma : Type where
| Gamma_Cons : SGammaEntry -> SGamma -> SGamma
| Gamma_End : SGamma
deriving Repr

inductive SPsiEntry : Type where
| PsiCorr : SLabel -> SPsiEntry
| PsiNotCorr : SLabel -> SPsiEntry
deriving Repr

inductive SPsi : Type where
| Psi_Cons : SPsiEntry -> SPsi -> SPsi
| Psi_End : SPsi
