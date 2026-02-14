import OwlLean.TypeChecker.OwlSExpr
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.TcSimple

open Lean Elab Meta

deriving instance ToExpr for SLabel
deriving instance ToExpr for SCondSym
deriving instance ToExpr for SRexp
deriving instance ToExpr for SProp
deriving instance ToExpr for STy

declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_constr
declare_syntax_cat owl_cond_sym
declare_syntax_cat owl_phi
declare_syntax_cat owl_phi_entry
declare_syntax_cat owl_delta
declare_syntax_cat owl_gamma
declare_syntax_cat owl_delta_entry
declare_syntax_cat owl_gamma_entry
declare_syntax_cat owl_psi_entry
declare_syntax_cat owl_psi
declare_syntax_cat owl_rexp

-- syntax for labels
syntax ident : owl_label
syntax "⟨" term "⟩"  : owl_label
syntax "⊥" : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "$" term:max "[" owl_label,* "]" : owl_label
syntax "$" term:max : owl_label
syntax "(" owl_label ")" : owl_label



partial def elabLabel : Syntax → TermElabM Expr
  | `(owl_label| ( $e:owl_label)) => elabLabel e
  | `(owl_label| ⟨ $t:term ⟩ ) => do
      let t' ← Term.elabTerm t (mkConst ``Owl.Lcarrier)
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
  | `(owl_label| $ $l:term [ $xs:owl_label,* ] ) => do
      let xs' <- xs.getElems.mapM elabLabel
      let xs_list <- mkListLit (mkConst ``SLabel) xs'.toList
      let l' ← Term.elabTerm l (mkConst ``Owl.label)
      mkAppM ``SLabel.embedlabel #[l', xs_list]
  | `(owl_label| $ $l:term ) => do
      let empty_list <- mkListLit (mkConst ``SLabel) []
      let l' ← Term.elabTerm l (mkConst ``Owl.label)
      mkAppM ``SLabel.embedlabel #[l', empty_list]
  | `(owl_label| ⊥) =>
      let b := Owl.L.bot;
      mkAppM ``SLabel.latl #[toExpr b]
  | _ => throwUnsupportedSyntax

-- syntax for cond symbols
syntax "⊑" : owl_cond_sym
syntax "⊒" : owl_cond_sym
syntax "⊏" : owl_cond_sym
syntax "⊐" : owl_cond_sym
syntax "!⊑" : owl_cond_sym
syntax "!⊒" : owl_cond_sym
syntax "!⊏" : owl_cond_sym
syntax "!⊐" : owl_cond_sym

partial def elabCondSym : Syntax → TermElabM Expr
  | `(owl_cond_sym| ⊑) => mkAppM ``SCondSym.leq #[]
  | `(owl_cond_sym| ⊒) => mkAppM ``SCondSym.geq #[]
  | `(owl_cond_sym| ⊏) => mkAppM ``SCondSym.lt #[]
  | `(owl_cond_sym| ⊐) => mkAppM ``SCondSym.gt #[]
  | `(owl_cond_sym| !⊑) => mkAppM ``SCondSym.nleq #[]
  | `(owl_cond_sym| !⊒) => mkAppM ``SCondSym.ngeq #[]
  | `(owl_cond_sym| !⊏) => mkAppM ``SCondSym.nlt #[]
  | `(owl_cond_sym| !⊐) => mkAppM ``SCondSym.ngt #[]
  | _ => throwUnsupportedSyntax

-- syntax for contraints
syntax "(" owl_constr ")" : owl_constr
syntax owl_label owl_cond_sym owl_label : owl_constr

partial def elabConstr : Syntax → TermElabM Expr
  | `(owl_constr| ( $e:owl_constr)) => elabConstr e
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let elab_l1 <- elabLabel l1
      let elab_l2 <- elabLabel l2
      let elab_c <- elabCondSym c
      mkAppM ``SConstr.condition #[elab_c, elab_l1, elab_l2]
  | _ => throwUnsupportedSyntax


syntax ident : owl_rexp
syntax "val(" ident ")" : owl_rexp
syntax ident "(" owl_rexp "," owl_rexp ")" : owl_rexp
syntax str : owl_rexp


partial def elab_rexp : Syntax -> TermElabM Expr
  | `(owl_rexp | $op:ident ( $e1, $e2 )) => do
    let r1 <- elab_rexp e1
    let r2 <- elab_rexp e2
    mkAppM ``SRexp.op #[mkStrLit op.getId.toString, r1, r2]
  | `(owl_rexp | val($i)) =>
    mkAppM ``SRexp.tmvar #[mkStrLit i.getId.toString]
  | `(owl_rexp | $i:ident ) => do
    mkAppM ``SRexp.var #[mkStrLit i.getId.toString]
  | `(owl_rexp |  $ob:str  ) => do
    mkAppM ``SRexp.const #[mkStrLit ob.getString]
  | _ => throwUnsupportedSyntax


declare_syntax_cat owl_prop
syntax "(" owl_prop ")" : owl_prop
syntax owl_rexp "=" owl_rexp : owl_prop
syntax owl_prop "∧" owl_prop : owl_prop
syntax owl_prop "∨" owl_prop : owl_prop
syntax owl_prop "→" owl_prop : owl_prop
syntax "¬" owl_prop : owl_prop
syntax "∀" ident "." owl_prop : owl_prop

partial def elab_prop : Syntax -> TermElabM Expr
  | `(owl_prop| ( $e:owl_prop )) => elab_prop e
  | `(owl_prop| $e1:owl_rexp = $e2:owl_rexp) => do
    let r1 <- elab_rexp e1
    let r2 <- elab_rexp e2
    mkAppM ``SProp.peq #[r1, r2]
  | `(owl_prop| $p1:owl_prop ∧ $p2:owl_prop) => do
    let ep1 <- elab_prop p1
    let ep2 <- elab_prop p2
    mkAppM ``SProp.pand #[ep1, ep2]
  | `(owl_prop| $p1:owl_prop ∨ $p2:owl_prop) => do
    let ep1 <- elab_prop p1
    let ep2 <- elab_prop p2
    mkAppM ``SProp.por #[ep1, ep2]
  | `(owl_prop| $p1:owl_prop → $p2:owl_prop) => do
    let ep1 <- elab_prop p1
    let ep2 <- elab_prop p2
    mkAppM ``SProp.pimpl #[ep1, ep2]
  | `(owl_prop| ¬ $p:owl_prop) => do
    let ep <- elab_prop p
    mkAppM ``SProp.pnot #[ep]
  | `(owl_prop| ∀ $x:ident . $p:owl_prop ) => do
    let p' <- elab_prop p
    mkAppM ``SProp.pall #[mkStrLit x.getId.toString, p']


  | _ => throwUnsupportedSyntax

-- syntax for types
syntax "(" owl_type ")" : owl_type
syntax ident : owl_type
syntax "Any" : owl_type
syntax "unit" : owl_type
syntax "RData" owl_label "[" owl_rexp "]" : owl_type
syntax "Data" owl_label : owl_type
syntax "Ref" owl_type : owl_type
syntax owl_type "->" owl_type : owl_type
syntax owl_type "*" owl_type : owl_type
syntax owl_type "+" owl_type : owl_type
syntax owl_type "∪" owl_type : owl_type
syntax owl_type "∩" owl_type : owl_type
syntax "∀" ident "<:" owl_type "." owl_type : owl_type
syntax "∃" ident "<:" owl_type "." owl_type : owl_type
syntax "∀" ident owl_cond_sym owl_label "." owl_type : owl_type
syntax "∃" ident "." owl_type : owl_type
syntax "∀" ident "." owl_type : owl_type
syntax "corr" "(" owl_label ")" "?" owl_type ":" owl_type : owl_type
syntax "Public" : owl_type
syntax "$" term:max "[" owl_label,* "]" "[" owl_type,* "]" : owl_type
syntax owl_type "{" owl_prop "}" : owl_type

partial def elabType : Syntax → TermElabM Expr
  | `(owl_type| ( $e:owl_type)) => elabType e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| unit) => mkAppM ``STy.Unit #[]
  | `(owl_type| Public) => mkAppM ``STy.Public #[]
  | `(owl_type| Data $l:owl_label ) => do
    let elab_l <- elabLabel l
    mkAppM ``STy.Data #[elab_l]
  | `(owl_type| RData $l:owl_label [ $re ] ) => do
    let elab_l <- elabLabel l
    let elab_r <- elab_rexp re
    mkAppM ``STy.RData #[elab_l, elab_r]
  | `(owl_type| Ref $t:owl_type) => do
    let elab_t <- elabType t
    mkAppM ``STy.Ref #[elab_t]
  | `(owl_type| $t1:owl_type -> $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.arr #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type * $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.prod #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type + $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.sum #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type ∪ $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.union #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type ∩ $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.inter #[elab_t1, elab_t2]
  | `(owl_type| ∀ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.all #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∃ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    mkAppM ``STy.ex #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∃ $id:ident . $t2:owl_type) => do
    let t2' <- elabType t2
    mkAppM ``STy.ex_r #[mkStrLit id.getId.toString, t2']
  | `(owl_type| ∀ $id:ident . $t2:owl_type) => do
    let t2' <- elabType t2
    mkAppM ``STy.all_r #[mkStrLit id.getId.toString, t2']
  | `(owl_type| ∀ $id:ident $c:owl_cond_sym $l:owl_label . $t:owl_type) => do
    let elab_t <- elabType t
    let elab_l <- elabLabel l
    let elab_c <- elabCondSym c
    mkAppM ``STy.all_l #[mkStrLit id.getId.toString, elab_c, elab_l, elab_t]
  | `(owl_type| corr ( $c:owl_label ) ? $t1:owl_type : $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    let elab_c <- elabLabel c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | `(owl_type| $ $t:term [ $ls:owl_label,* ] [ $ts:owl_type,* ]) => do
    let ls' <- ls.getElems.mapM elabLabel
    let ts' <- ts.getElems.mapM elabType
    let ls_list <- mkListLit (mkConst ``SLabel) ls'.toList
    let ts_list <- mkListLit (mkConst ``STy) ts'.toList
    let t' ← Term.elabTerm t (mkConst ``Owl.ty)
    mkAppM ``STy.embedty #[t', ls_list, ts_list]
  | `(owl_type| $t:owl_type { $p }) => do
    let elab_t ← elabType t
    let elab_p <- elab_prop p
    mkAppM ``STy.refined #[elab_t, elab_p]
  | _ => throwError "Unexpected syntax for elabType"

notation:100 "PURE" => pure ()
notation:100 "THROW" => throw ()

-- syntax for terms
syntax "(" owl_tm ")" : owl_tm
syntax ident : owl_tm
syntax num : owl_tm
syntax "error" : owl_tm
syntax "()" : owl_tm
syntax str : owl_tm
syntax "fix" ident "(" ident ")" owl_tm : owl_tm
syntax "Λ" owl_type "." owl_tm : owl_tm
syntax "Λβ" owl_label "." owl_tm : owl_tm
syntax "Λr" ident "." owl_tm : owl_tm
syntax "⟨" owl_tm "," owl_tm "⟩" : owl_tm
syntax "⟨" term "⟩" "(" owl_tm "," owl_tm ")" : owl_tm -- Op case
syntax "zero" owl_tm : owl_tm
syntax owl_tm "[" owl_tm "]" : owl_tm
syntax "alloc" owl_tm : owl_tm
syntax "!" owl_tm : owl_tm
syntax owl_tm ":=" owl_tm : owl_tm
syntax "π1" owl_tm : owl_tm
syntax "π2" owl_tm : owl_tm
syntax "ı1" owl_tm : owl_tm
syntax "ı2" owl_tm : owl_tm
syntax "case" owl_tm "in" "|" "inl" owl_tm "=>" owl_tm "|" "inr" owl_tm "=>" owl_tm : owl_tm
syntax owl_tm "[[" owl_type "]]" : owl_tm
syntax owl_tm "[{" owl_rexp "}]" : owl_tm
syntax owl_tm "[[[" owl_label "]]]" : owl_tm
syntax "pack" "(" owl_type "," owl_tm ")" : owl_tm
syntax "rpack" "(" owl_rexp "," owl_tm ")" : owl_tm
syntax "unpack" owl_tm "as" "(" ident "," ident ")" "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" "corr" "(" owl_label ")" "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm
syntax "union_elim" ident "=" owl_tm "in" owl_tm : owl_tm
syntax "let" ident "=" owl_tm "in" owl_tm : owl_tm
syntax "let" ident ":" owl_type "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" ident "," ident ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" ident "," ident "," ident ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "λ" "(" ident ":" owl_type ")" ":" owl_type "=>" owl_tm : owl_tm
syntax "λ" ident "=>" owl_tm : owl_tm
syntax "$" term:max "[" owl_label,* "]" "[" owl_type,* "]" "[" owl_tm,* "]" : owl_tm
syntax "corr_case" owl_label "in" owl_tm : owl_tm
syntax "(" owl_tm ":" owl_type ")" : owl_tm

-- ALLOW : let (x , y) = e in ...
-- expands to :
-- let e' = e in
-- let x = π1 e' in
-- let y = π2 e' in ...

deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax

def mkOpaqueSyntax (s : Lean.Syntax) : Owl.opaqueSyntax := { inner := s }

def mkEmptySyntax : String ->  TermElabM Expr := fun s =>
  mkAppM ``mkOpaqueSyntax #[toExpr (Syntax.atom SourceInfo.none s)]

mutual
  partial def elabTm : Syntax -> TermElabM Expr :=
    fun stx => do
      let se <- mkAppM ``mkOpaqueSyntax #[toExpr stx]
      mkAppM ``SExpr.mk #[se, ← elabTmX stx]

partial def elabTmX : Syntax → TermElabM Expr
  | `(owl_tm| ( $e:owl_tm)) => elabTmX e
  | `(owl_tm| $id:ident) =>
        mkAppM ``SExprX.var_tm #[mkStrLit id.getId.toString]
  | `(owl_tm| $n:num) =>
    mkAppM ``SExprX.loc #[mkNatLit n.getNat]
  | `(owl_tm| error) => mkAppM ``SExprX.error #[]
  | `(owl_tm| ()) => mkAppM ``SExprX.skip #[]
  | `(owl_tm| $b:str  ) => do
    mkAppM ``SExprX.bitstring #[mkStrLit b.getString]
  | `(owl_tm| fix $f:ident ( $id:ident ) $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.fixlam #[mkStrLit f.getId.toString, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.tlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λβ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.l_lam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λr $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.rlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.tm_pair #[elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let t' ← Term.elabTerm t (mkConst ``String)
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.Op #[t', elab_e1, elab_e2]
  | `(owl_tm| zero $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.zero #[elab_e]
  | `(owl_tm| $e1:owl_tm [ $e2:owl_tm ]) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.app #[elab_e1, elab_e2]
  | `(owl_tm| alloc $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.alloc #[elab_e]
  | `(owl_tm| ! $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.dealloc #[elab_e]
  | `(owl_tm| $e1:owl_tm := $e2:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.assign #[elab_e1, elab_e2]
  | `(owl_tm| π1 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.left_tm #[elab_e]
  | `(owl_tm| π2 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.right_tm #[elab_e]
  | `(owl_tm| ı1 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.inl #[elab_e]
  | `(owl_tm| ı2 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.inr #[elab_e]
  | `(owl_tm| case $e1:owl_tm in | inl $id1:ident => $e2:owl_tm | inr $id2:ident => $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExprX.case #[elab_e1, mkStrLit id1.getId.toString, elab_e2, mkStrLit id2.getId.toString, elab_e3]
  | `(owl_tm| $e:owl_tm [[ $t:owl_type ]]) => do
    let elab_e <- elabTm e
    let elab_t <- elabType t
    mkAppM ``SExprX.tapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [{ $r:owl_rexp }]) => do
    let elab_e <- elabTm e
    let elab_t <- elab_rexp r
    mkAppM ``SExprX.rapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [[[ $l:owl_label ]]]) => do
    let elab_e <- elabTm e
    let elab_l <- elabLabel l
    mkAppM ``SExprX.lapp #[elab_e, elab_l]
  | `(owl_tm| unpack $e1:owl_tm as ($id1:ident, $id2:ident) in $e2:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.unpack #[elab_e1, mkStrLit id1.getId.toString, mkStrLit id2.getId.toString, elab_e2]
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let elab_t <- elabType t
    let elab_e <- elabTm e
    mkAppM ``SExprX.pack #[elab_t, elab_e]
  | `(owl_tm| rpack ($re:owl_rexp, $e:owl_tm)) => do
    let elab_r <- elab_rexp re
    let elab_e <- elabTm e
    mkAppM ``SExprX.rpack #[elab_r, elab_e]
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExprX.if_tm #[elab_e1, elab_e2, elab_e3]
  | `(owl_tm| if corr($c:owl_label) then $e1:owl_tm else $e2:owl_tm) => do
    let elab_c <- elabLabel c
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.if_c #[elab_c, elab_e1, elab_e2]
  | `(owl_tm| sync $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.sync #[elab_e]
  | `(owl_tm| union_elim $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    mkAppM ``SExprX.union_elim #[mkStrLit id1.getId.toString, <- elabTm e, <- elabTm b]
  | `(owl_tm| let $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let elab_e <- elabTm e
    let elab_b <- elabTm b
    mkAppM ``SExprX.elet #[mkStrLit id1.getId.toString, elab_e, elab_b]
  | `(owl_tm| let $id1:ident : $t:owl_type = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm |
      let $id1 = ($e : $t) in $b
    ))
  | `(owl_tm| let ($id1:ident, $id2:ident) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm| let $id1 = π1 $e in let $id2 = π2 $e in $b))
  | `(owl_tm| let ($id1:ident, $id2:ident, $id3:ident) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm |
      let $id1 = π1 $e in
      let $id2 = π1 (π2 $e) in
      let $id3 = π2 (π2 $e) in
      $b
    ))
  | `(owl_tm| λ ($id:ident : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    elabTmX (<- `(owl_tm|
      ((λ $id => $e) : ($t1 -> $t2)
    )))
  | `(owl_tm| λ $id:ident => $e:owl_tm) => do
    let elab_e <- elabTm e
    let unused := "unused variable"
    mkAppM ``SExprX.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| corr_case $l1:owl_label in $e:owl_tm ) => do
    let elab_e <- elabTm e
    let elab_l1 <- elabLabel l1
    mkAppM ``SExprX.corr_case #[elab_l1, elab_e]
  | `(owl_tm| ( $e:owl_tm : $t:owl_type)) => do
    let elab_e <- elabTm e
    let elab_t <- elabType t
    mkAppM ``SExprX.annot #[elab_e, elab_t]
  | _ => throwUnsupportedSyntax
end

-- CLOSED ELABORATORS

partial def elabLabel_closed : Syntax → TermElabM Expr
  | `(owl_label| ( $e:owl_label)) => elabLabel_closed e
  | `(owl_label| ⟨ $_:term ⟩ ) => do mkAppM ``SLabel.default #[]
  | `(owl_label| $e1:owl_label ⊔ $e2:owl_label) => do
      let elab_e1 <- elabLabel_closed e1
      let elab_e2 <- elabLabel_closed e2
      mkAppM ``SLabel.ljoin #[elab_e1, elab_e2]
  | `(owl_label| $e1:owl_label ⊓ $e2:owl_label) => do
      let elab_e1 <- elabLabel_closed e1
      let elab_e2 <- elabLabel_closed e2
      mkAppM ``SLabel.lmeet #[elab_e1, elab_e2]
  | `(owl_label| $id:ident) =>
    mkAppM ``SLabel.var_label #[mkStrLit id.getId.toString]
  | `(owl_label| $ $l:term [ $xs:owl_label,* ]  ) => do
      let xs' <- xs.getElems.mapM elabLabel_closed
      let xs_list <- mkListLit (mkConst ``SLabel) xs'.toList
      let l' ← Term.elabTerm l (mkConst ``Owl.label)
      mkAppM ``SLabel.embedlabel #[l', xs_list]
  | `(owl_label| $ $l:term ) => do
      let empty_list <- mkListLit (mkConst ``SLabel) []
      let l' ← Term.elabTerm l (mkConst ``Owl.label)
      mkAppM ``SLabel.embedlabel #[l', empty_list]
  | `(owl_label| ⊥) =>
      let b := Owl.L.bot;
      mkAppM ``SLabel.latl #[toExpr b]
  | _ => throwUnsupportedSyntax

partial def elabConstr_closed : Syntax → TermElabM Expr
  | `(owl_constr| ( $e:owl_constr)) => elabConstr_closed e
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let elab_l1 <- elabLabel_closed l1
      let elab_l2 <- elabLabel_closed l2
      let elab_c <- elabCondSym c
      mkAppM ``SConstr.condition #[elab_c, elab_l1, elab_l2]
  | _ => throwUnsupportedSyntax

partial def elabType_closed : Syntax → TermElabM Expr
  | `(owl_type| ( $e:owl_type)) => elabType_closed e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| unit) => mkAppM ``STy.Unit #[]
  | `(owl_type| Public) => mkAppM ``STy.Public #[]
  | `(owl_type| RData $l:owl_label [ $re ] ) => do
    let elab_l <- elabLabel_closed l
    let elab_r <- elab_rexp re
    mkAppM ``STy.RData #[elab_l, elab_r ]
  | `(owl_type| Data $l:owl_label ) => do
    let elab_l <- elabLabel_closed l
    mkAppM ``STy.Data #[elab_l]
  | `(owl_type| Ref $t:owl_type) => do
    let elab_t <- elabType_closed t
    mkAppM ``STy.Ref #[elab_t]
  | `(owl_type| $t1:owl_type -> $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    mkAppM ``STy.arr #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type * $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    mkAppM ``STy.prod #[elab_t1, elab_t2]
  | `(owl_type| $t1:owl_type + $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    mkAppM ``STy.sum #[elab_t1, elab_t2]
  | `(owl_type| ∀ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    mkAppM ``STy.all #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∃ $id:ident <: $t1:owl_type . $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    mkAppM ``STy.ex #[mkStrLit id.getId.toString, elab_t1, elab_t2]
  | `(owl_type| ∀ $id:ident $c:owl_cond_sym $l:owl_label . $t:owl_type) => do
    let elab_t <- elabType_closed t
    let elab_l <- elabLabel_closed l
    let elab_c <- elabCondSym c
    mkAppM ``STy.all_l #[mkStrLit id.getId.toString, elab_c, elab_l, elab_t]
  | `(owl_type| ∃ $id:ident . $t2:owl_type) => do
    let t2' <- elabType_closed t2
    mkAppM ``STy.ex_r #[mkStrLit id.getId.toString, t2']
  | `(owl_type| ∀ $id:ident . $t2:owl_type) => do
    let t2' <- elabType_closed t2
    mkAppM ``STy.all_r #[mkStrLit id.getId.toString, t2']
  | `(owl_type| corr ( $c:owl_label ) ? $t1:owl_type : $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    let elab_c <- elabLabel_closed c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | `(owl_type| $ $_:term [$_:owl_label,* ] [$_:owl_type,*]) => mkAppM ``STy.default #[]
  | `(owl_type| $t:owl_type { $p }) => do
    let elab_t ← elabType t
    let elab_p <- elab_prop p
    mkAppM ``STy.refined #[elab_t, elab_p]
  | _ => throwUnsupportedSyntax


mutual

  partial def elabTm_closed : Syntax -> TermElabM Expr :=
    fun stx => do
      let se <- mkAppM ``mkOpaqueSyntax #[toExpr stx]
      -- let se <- mkEmptySyntax s!"elabTm_closed {stx.prettyPrint}"
      mkAppM ``SExpr.mk #[se, ← elabTmX_closed stx]

partial def elabTmX_closed : Syntax → TermElabM Expr
  | `(owl_tm| ( $e:owl_tm)) => elabTmX_closed e
  | `(owl_tm| $id:ident) =>
        mkAppM ``SExprX.var_tm #[mkStrLit id.getId.toString]
  | `(owl_tm| $n:num) =>
    mkAppM ``SExprX.loc #[mkNatLit n.getNat]
  | `(owl_tm| error) => mkAppM ``SExprX.error #[]
  | `(owl_tm| ()) => mkAppM ``SExprX.skip #[]
  | `(owl_tm| $b:str ) => do
    mkAppM ``SExprX.bitstring #[mkStrLit b.getString]
  | `(owl_tm| fix $f:ident ( $id:ident ) $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.fixlam #[mkStrLit f.getId.toString, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.tlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λβ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.l_lam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λr $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.rlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.tm_pair #[elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let t' ← Term.elabTerm t (mkConst ``String)
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.Op #[t', elab_e1, elab_e2]
  | `(owl_tm| $ $_:term [ $_:owl_label,* ] [ $_:owl_type,* ] [ $_:owl_tm,* ]) => mkAppM ``SExprX.default #[]
  | `(owl_tm| zero $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.zero #[elab_e]
  | `(owl_tm| $e1:owl_tm [ $e2:owl_tm ]) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.app #[elab_e1, elab_e2]
  | `(owl_tm| alloc $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.alloc #[elab_e]
  | `(owl_tm| ! $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.dealloc #[elab_e]
  | `(owl_tm| $e1:owl_tm := $e2:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.assign #[elab_e1, elab_e2]
  | `(owl_tm| π1 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.left_tm #[elab_e]
  | `(owl_tm| π2 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.right_tm #[elab_e]
  | `(owl_tm| ı1 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.inl #[elab_e]
  | `(owl_tm| ı2 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.inr #[elab_e]
  | `(owl_tm| case $e1:owl_tm in | inl $id1:ident => $e2:owl_tm | inr $id2:ident => $e3:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    let elab_e3 <- elabTm_closed e3
    mkAppM ``SExprX.case #[elab_e1, mkStrLit id1.getId.toString, elab_e2, mkStrLit id2.getId.toString, elab_e3]
  | `(owl_tm| $e:owl_tm [[ $t:owl_type ]]) => do
    let elab_e <- elabTm_closed e
    let elab_t <- elabType_closed t
    mkAppM ``SExprX.tapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [{ $r:owl_rexp }]) => do
    let elab_e <- elabTm_closed e
    let elab_t <- elab_rexp r
    mkAppM ``SExprX.rapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [[[ $l:owl_label ]]]) => do
    let elab_e <- elabTm_closed e
    let elab_l <- elabLabel l
    mkAppM ``SExprX.lapp #[elab_e, elab_l]
  | `(owl_tm| unpack $e1:owl_tm as ($id1:ident, $id2:ident) in $e2:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.unpack #[elab_e1, mkStrLit id1.getId.toString, mkStrLit id2.getId.toString, elab_e2]
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let elab_t <- elabType_closed t
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.pack #[elab_t, elab_e]
  | `(owl_tm| rpack ($re:owl_rexp, $e:owl_tm)) => do
    let elab_r <- elab_rexp re
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.rpack #[elab_r, elab_e]
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    let elab_e3 <- elabTm_closed e3
    mkAppM ``SExprX.if_tm #[elab_e1, elab_e2, elab_e3]
  | `(owl_tm| if corr($c:owl_label) then $e1:owl_tm else $e2:owl_tm) => do
    let elab_c <- elabLabel_closed c
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExprX.if_c #[elab_c, elab_e1, elab_e2]
  | `(owl_tm| sync $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExprX.sync #[elab_e]
  | `(owl_tm| let $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let elab_e <- elabTm_closed e
    let elab_b <- elabTm_closed b
    mkAppM ``SExprX.elet #[mkStrLit id1.getId.toString, elab_e, elab_b]
  | `(owl_tm| let $id1:ident : $t:owl_type = $e:owl_tm  in $b:owl_tm) => do
    elabTmX_closed (<- `(owl_tm |
      let $id1 = ($e : $t) in $b
    ))
  | `(owl_tm| let ($id1:ident, $id2:ident) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX_closed (<- `(owl_tm| let $id1 = π1 $e in let $id2 = π2 $e in $b))
  | `(owl_tm| let ($id1:ident, $id2:ident, $id3:ident) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX_closed (<- `(owl_tm |
      let $id1 = π1 $e in
      let $id2 = π1 (π2 $e) in
      let $id3 = π2 (π2 $e) in
      $b
    ))
  | `(owl_tm| λ ($id:ident : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    elabTmX_closed (<- `(owl_tm|
      ((λ $id => $e) : ($t1 -> $t2)
    )))
  | `(owl_tm| λ $id:ident => $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    let unused := "unused variable"
    mkAppM ``SExprX.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| corr_case $l1:owl_label in $e:owl_tm ) => do
    let elab_e <- elabTm_closed e
    let elab_l1 <- elabLabel_closed l1
    mkAppM ``SExprX.corr_case #[elab_l1, elab_e]
  | `(owl_tm| ( $e:owl_tm : $t:owl_type)) => do
    let elab_e <- elabTm_closed e
    let elab_t <- elabType_closed t
    mkAppM ``SExprX.annot #[elab_e, elab_t]
  | _ => throwUnsupportedSyntax
end

-- Phi Mappings
syntax "(" owl_phi_entry ")" : owl_phi_entry
syntax  ident owl_cond_sym owl_label : owl_phi_entry
syntax ident : owl_phi_entry

partial def elabPhiEntry : Syntax → TermElabM Expr
  | `(owl_phi_entry| ( $e:owl_phi_entry)) => elabPhiEntry e
  | `(owl_phi_entry|  $id:ident $co:owl_cond_sym $lab:owl_label) => do
      let elab_co <- elabCondSym co
      let elab_lab <- elabLabel lab
      mkAppM ``SPhiEntry.PhiEntry #[mkStrLit id.getId.toString, elab_co, elab_lab]
  | `(owl_phi_entry| $id:ident) => do
      let condSym <- mkAppM ``SCondSym.geq #[]
      let botExpr := mkApp (mkConst ``Owl.Lattice.bot) (mkConst ``Owl.L)
      let botLExpr <- mkAppM ``SLabel.latl #[botExpr]
      mkAppM ``SPhiEntry.PhiEntry #[mkStrLit id.getId.toString, condSym, botLExpr]
  | _ => throwUnsupportedSyntax

partial def elabPhiEntry_closed : Syntax → TermElabM Expr
  | `(owl_phi_entry| ( $e:owl_phi_entry)) => elabPhiEntry_closed e
  | `(owl_phi_entry|  $id:ident $co:owl_cond_sym $lab:owl_label) => do
      let elab_co <- elabCondSym co
      let elab_lab <- elabLabel_closed lab
      mkAppM ``SPhiEntry.PhiEntry #[mkStrLit id.getId.toString, elab_co, elab_lab]
  | `(owl_phi_entry| $id:ident) => do
      let condSym <- mkAppM ``SCondSym.geq #[]
      let botExpr <- mkAppM ``SLabel.default #[]
      mkAppM ``SPhiEntry.PhiEntry #[mkStrLit id.getId.toString, condSym, botExpr]
  | _ => throwUnsupportedSyntax

syntax "(" owl_delta_entry ")" : owl_delta_entry
syntax  ident "<:" owl_type : owl_delta_entry

partial def elabDeltaEntry : Syntax → TermElabM Expr
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaEntry e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let elab_t <- elabType t
      mkAppM ``SDeltaEntry.DeltaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

partial def elabDeltaEntry_closed : Syntax → TermElabM Expr
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaEntry_closed e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let elab_t <- elabType_closed t
      mkAppM ``SDeltaEntry.DeltaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

syntax "(" owl_gamma_entry ")" : owl_gamma_entry
syntax  ident "=>" owl_type : owl_gamma_entry

partial def elabGammaEntry : Syntax → TermElabM Expr
  | `(owl_gamma_entry| ( $e:owl_gamma_entry)) => elabGammaEntry e
  | `(owl_gamma_entry|  $id:ident => $t:owl_type) => do
      let elab_t <- elabType t
      mkAppM ``SGammaEntry.GammaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

partial def elabGammaEntry_closed : Syntax → TermElabM Expr
  | `(owl_gamma_entry| ( $e:owl_gamma_entry)) => elabGammaEntry_closed e
  | `(owl_gamma_entry|  $id:ident => $t:owl_type) => do
      let elab_t <- elabType_closed t
      mkAppM ``SGammaEntry.GammaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

syntax "(" owl_psi_entry ")" : owl_psi_entry
syntax  "corr(" owl_label ")" : owl_psi_entry
syntax  "¬corr(" owl_label ")" : owl_psi_entry

partial def elabPsiEntry : Syntax → TermElabM Expr
  | `(owl_psi_entry| ( $e:owl_psi_entry)) => elabPsiEntry e
  | `(owl_psi_entry| corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel l1
      mkAppM ``SPsiEntry.PsiCorr #[elab_l1]
      | `(owl_psi_entry| ¬corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel l1
      mkAppM ``SPsiEntry.PsiNotCorr #[elab_l1]
  | _ => throwUnsupportedSyntax

partial def elabPsiEntry_closed : Syntax → TermElabM Expr
  | `(owl_psi_entry| ( $e:owl_psi_entry)) => elabPsiEntry_closed e
  | `(owl_psi_entry| corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel_closed l1
      mkAppM ``SPsiEntry.PsiCorr #[elab_l1]
      | `(owl_psi_entry| ¬corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel_closed l1
      mkAppM ``SPsiEntry.PsiNotCorr #[elab_l1]
  | _ => throwUnsupportedSyntax

declare_syntax_cat owl_theta

syntax "·" : owl_theta
syntax owl_theta "," ident : owl_theta
syntax owl_theta "," owl_prop : owl_theta

partial def elabTheta : Syntax -> TermElabM Expr
  | `(owl_theta | · ) =>
    return (mkConst ``STheta.End)
  | `(owl_theta | $th, $x:ident) => do
    mkAppM ``STheta.STheta_var #[<- elabTheta th, mkStrLit x.getId.toString]
  | `(owl_theta | $th , $p ) => do
    mkAppM ``STheta.STheta_prop #[<- elabTheta th, <- elab_prop p]
  | _ => throwUnsupportedSyntax



syntax "(" owl_phi_entry "," owl_phi ")" : owl_phi
syntax owl_phi_entry "," owl_phi : owl_phi
syntax owl_phi_entry : owl_phi
syntax "(" owl_phi_entry ")" : owl_phi
syntax "·" : owl_phi

-- a nice and simple reversal
@[simp]
def SPhi.reverse (phi : SPhi) : SPhi :=
  go phi Phi_End
where
  @[simp]
  go : SPhi → SPhi → SPhi
  | Phi_End, acc => acc
  | Phi_Cons x xs, acc => go xs (Phi_Cons x acc)

@[simp]
def SDelta.reverse (delta : SDelta) : SDelta :=
  go delta Delta_End
where
  @[simp]
  go : SDelta → SDelta → SDelta
  | Delta_End, acc => acc
  | Delta_Cons x xs, acc => go xs (Delta_Cons x acc)

@[simp]
def SGamma.reverse (gamma : SGamma) : SGamma :=
  go gamma Gamma_End
where
  @[simp]
  go : SGamma → SGamma → SGamma
  | Gamma_End, acc => acc
  | Gamma_Cons x xs, acc => go xs (Gamma_Cons x acc)

partial def elabPhiHelper : Syntax → TermElabM Expr
  | `(owl_phi| ($e1:owl_phi_entry, $rest:owl_phi)) => do
    let elab_e1 ← elabPhiEntry e1
    let elab_rest ← elabPhiHelper rest
    mkAppM ``SPhi.Phi_Cons #[elab_e1, elab_rest]
  | `(owl_phi| $e1:owl_phi_entry , $rest:owl_phi) => do
    let elab_e1 ← elabPhiEntry e1
    let elab_rest ← elabPhiHelper rest
    mkAppM ``SPhi.Phi_Cons #[elab_e1, elab_rest]
  | `(owl_phi| $e:owl_phi_entry) => do
    let elab_e ← elabPhiEntry e
    let phiEnd ← mkAppM ``SPhi.Phi_End #[]
    mkAppM ``SPhi.Phi_Cons #[elab_e, phiEnd]
  | `(owl_phi| ($e:owl_phi_entry) ) => do
    let elab_e ← elabPhiEntry e
    let phiEnd ← mkAppM ``SPhi.Phi_End #[]
    mkAppM ``SPhi.Phi_Cons #[elab_e, phiEnd]
  | `(owl_phi| · ) => do
     mkAppM ``SPhi.Phi_End #[]
  | _ => throwUnsupportedSyntax

partial def elabPhiHelper_closed : Syntax → TermElabM Expr
  | `(owl_phi| ($e1:owl_phi_entry, $rest:owl_phi)) => do
    let elab_e1 ← elabPhiEntry_closed e1
    let elab_rest ← elabPhiHelper_closed rest
    mkAppM ``SPhi.Phi_Cons #[elab_e1, elab_rest]
  | `(owl_phi| $e1:owl_phi_entry , $rest:owl_phi) => do
    let elab_e1 ← elabPhiEntry_closed e1
    let elab_rest ← elabPhiHelper_closed rest
    mkAppM ``SPhi.Phi_Cons #[elab_e1, elab_rest]
  | `(owl_phi| $e:owl_phi_entry) => do
    let elab_e ← elabPhiEntry_closed e
    let phiEnd ← mkAppM ``SPhi.Phi_End #[]
    mkAppM ``SPhi.Phi_Cons #[elab_e, phiEnd]
  | `(owl_phi| ($e:owl_phi_entry) ) => do
    let elab_e ← elabPhiEntry_closed e
    let phiEnd ← mkAppM ``SPhi.Phi_End #[]
    mkAppM ``SPhi.Phi_Cons #[elab_e, phiEnd]
  | `(owl_phi| · ) => do
     mkAppM ``SPhi.Phi_End #[]
  | _ => throwUnsupportedSyntax

syntax "(" owl_delta_entry "," owl_delta ")" : owl_delta
syntax owl_delta_entry "," owl_delta : owl_delta
syntax owl_delta_entry : owl_delta
syntax "(" owl_delta_entry ")" : owl_delta
syntax "·" : owl_delta

partial def elabDeltaHelper : Syntax → TermElabM Expr
  | `(owl_delta| ($e1:owl_delta_entry, $rest:owl_delta)) => do
    let elab_e1 ← elabDeltaEntry e1
    let elab_rest ← elabDeltaHelper rest
    mkAppM ``SDelta.Delta_Cons #[elab_e1, elab_rest]
  | `(owl_delta| $e1:owl_delta_entry , $rest:owl_delta) => do
    let elab_e1 ← elabDeltaEntry e1
    let elab_rest ← elabDeltaHelper rest
    mkAppM ``SDelta.Delta_Cons #[elab_e1, elab_rest]
  | `(owl_delta| $e:owl_delta_entry) => do
    let elab_e ← elabDeltaEntry e
    let phiEnd ← mkAppM ``SDelta.Delta_End #[]
    mkAppM ``SDelta.Delta_Cons #[elab_e, phiEnd]
  | `(owl_delta| ($e:owl_delta_entry) ) => do
    let elab_e ← elabDeltaEntry e
    let deltaEnd ← mkAppM ``SDelta.Delta_End #[]
    mkAppM ``SDelta.Delta_Cons #[elab_e, deltaEnd]
  | `(owl_delta| · ) => do
     mkAppM ``SDelta.Delta_End #[]
  | _ => throwUnsupportedSyntax

partial def elabDeltaHelper_closed : Syntax → TermElabM Expr
  | `(owl_delta| ($e1:owl_delta_entry, $rest:owl_delta)) => do
    let elab_e1 ← elabDeltaEntry_closed e1
    let elab_rest ← elabDeltaHelper_closed rest
    mkAppM ``SDelta.Delta_Cons #[elab_e1, elab_rest]
  | `(owl_delta| $e1:owl_delta_entry , $rest:owl_delta) => do
    let elab_e1 ← elabDeltaEntry_closed e1
    let elab_rest ← elabDeltaHelper_closed rest
    mkAppM ``SDelta.Delta_Cons #[elab_e1, elab_rest]
  | `(owl_delta| $e:owl_delta_entry) => do
    let elab_e ← elabDeltaEntry_closed e
    let phiEnd ← mkAppM ``SDelta.Delta_End #[]
    mkAppM ``SDelta.Delta_Cons #[elab_e, phiEnd]
  | `(owl_delta| ($e:owl_delta_entry) ) => do
    let elab_e ← elabDeltaEntry_closed e
    let deltaEnd ← mkAppM ``SDelta.Delta_End #[]
    mkAppM ``SDelta.Delta_Cons #[elab_e, deltaEnd]
  | `(owl_delta| · ) => do
     mkAppM ``SDelta.Delta_End #[]
  | _ => throwUnsupportedSyntax

syntax "(" owl_gamma_entry "," owl_gamma ")" : owl_gamma
syntax owl_gamma_entry "," owl_gamma : owl_gamma
syntax owl_gamma_entry : owl_gamma
syntax "(" owl_gamma_entry ")" : owl_gamma
syntax "·" : owl_gamma

partial def elabGammaHelper : Syntax → TermElabM Expr
  | `(owl_gamma| ($e1:owl_gamma_entry, $rest:owl_gamma)) => do
    let elab_e1 ← elabGammaEntry e1
    let elab_rest ← elabGammaHelper rest
    mkAppM ``SGamma.Gamma_Cons #[elab_e1, elab_rest]
  | `(owl_gamma| $e1:owl_gamma_entry , $rest:owl_gamma) => do
    let elab_e1 ← elabGammaEntry e1
    let elab_rest ← elabGammaHelper rest
    mkAppM ``SGamma.Gamma_Cons #[elab_e1, elab_rest]
  | `(owl_gamma| $e:owl_gamma_entry) => do
    let elab_e ← elabGammaEntry e
    let gammaEnd ← mkAppM ``SGamma.Gamma_End #[]
    mkAppM ``SGamma.Gamma_Cons #[elab_e, gammaEnd]
  | `(owl_gamma| ($e:owl_gamma_entry) ) => do
    let elab_e ← elabGammaEntry e
    let gammaEnd ← mkAppM ``SGamma.Gamma_End #[]
    mkAppM ``SGamma.Gamma_Cons #[elab_e, gammaEnd]
  | `(owl_gamma| · ) => do
     mkAppM ``SGamma.Gamma_End #[]
  | _ => throwUnsupportedSyntax

partial def elabGammaHelper_closed : Syntax → TermElabM Expr
  | `(owl_gamma| ($e1:owl_gamma_entry, $rest:owl_gamma)) => do
    let elab_e1 ← elabGammaEntry_closed e1
    let elab_rest ← elabGammaHelper_closed rest
    mkAppM ``SGamma.Gamma_Cons #[elab_e1, elab_rest]
  | `(owl_gamma| $e1:owl_gamma_entry , $rest:owl_gamma) => do
    let elab_e1 ← elabGammaEntry_closed e1
    let elab_rest ← elabGammaHelper_closed rest
    mkAppM ``SGamma.Gamma_Cons #[elab_e1, elab_rest]
  | `(owl_gamma| $e:owl_gamma_entry) => do
    let elab_e ← elabGammaEntry_closed e
    let gammaEnd ← mkAppM ``SGamma.Gamma_End #[]
    mkAppM ``SGamma.Gamma_Cons #[elab_e, gammaEnd]
  | `(owl_gamma| ($e:owl_gamma_entry) ) => do
    let elab_e ← elabGammaEntry_closed e
    let gammaEnd ← mkAppM ``SGamma.Gamma_End #[]
    mkAppM ``SGamma.Gamma_Cons #[elab_e, gammaEnd]
  | `(owl_gamma| · ) => do
     mkAppM ``SGamma.Gamma_End #[]
  | _ => throwUnsupportedSyntax

syntax "(" owl_psi_entry "," owl_psi ")" : owl_psi
syntax owl_psi_entry "," owl_psi : owl_psi
syntax owl_psi_entry : owl_psi
syntax "(" owl_psi_entry ")" : owl_psi
syntax "·" : owl_psi

partial def elabPsi : Syntax → TermElabM Expr
  | `(owl_psi| ($e1:owl_psi_entry, $rest:owl_psi)) => do
    let elab_e1 ← elabPsiEntry e1
    let elab_rest ← elabPsi rest
    mkAppM ``SPsi.Psi_Cons #[elab_e1, elab_rest]
  | `(owl_psi| $e1:owl_psi_entry , $rest:owl_psi) => do
    let elab_e1 ← elabPsiEntry e1
    let elab_rest ← elabPsi rest
    mkAppM ``SPsi.Psi_Cons #[elab_e1, elab_rest]
  | `(owl_psi| $e:owl_psi_entry) => do
    let elab_e ← elabPsiEntry e
    let psiEnd ← mkAppM ``SPsi.Psi_End #[]
    mkAppM ``SPsi.Psi_Cons #[elab_e, psiEnd]
  | `(owl_psi| ($e:owl_psi_entry) ) => do
    let elab_e ← elabPsiEntry e
    let psiEnd ← mkAppM ``SPsi.Psi_End #[]
    mkAppM ``SPsi.Psi_Cons #[elab_e, psiEnd]
  | `(owl_psi| · ) => do
     mkAppM ``SPsi.Psi_End #[]
  | _ => throwUnsupportedSyntax

partial def elabPsi_closed : Syntax → TermElabM Expr
  | `(owl_psi| ($e1:owl_psi_entry, $rest:owl_psi)) => do
    let elab_e1 ← elabPsiEntry_closed e1
    let elab_rest ← elabPsi_closed rest
    mkAppM ``SPsi.Psi_Cons #[elab_e1, elab_rest]
  | `(owl_psi| $e1:owl_psi_entry , $rest:owl_psi) => do
    let elab_e1 ← elabPsiEntry_closed e1
    let elab_rest ← elabPsi_closed rest
    mkAppM ``SPsi.Psi_Cons #[elab_e1, elab_rest]
  | `(owl_psi| $e:owl_psi_entry) => do
    let elab_e ← elabPsiEntry_closed e
    let psiEnd ← mkAppM ``SPsi.Psi_End #[]
    mkAppM ``SPsi.Psi_Cons #[elab_e, psiEnd]
  | `(owl_psi| ($e:owl_psi_entry) ) => do
    let elab_e ← elabPsiEntry_closed e
    let psiEnd ← mkAppM ``SPsi.Psi_End #[]
    mkAppM ``SPsi.Psi_Cons #[elab_e, psiEnd]
  | `(owl_psi| · ) => do
     mkAppM ``SPsi.Psi_End #[]
  | _ => throwUnsupportedSyntax

partial def elabPhi (stx : Syntax) : TermElabM Expr := do
  let phi ← elabPhiHelper stx
  mkAppM ``SPhi.reverse #[phi]

partial def elabPhi_closed (stx : Syntax) : TermElabM Expr := do
  let phi ← elabPhiHelper_closed stx
  mkAppM ``SPhi.reverse #[phi]

partial def elabDelta (stx : Syntax) : TermElabM Expr := do
  let delta ← elabDeltaHelper stx
  mkAppM ``SDelta.reverse #[delta]

partial def elabDelta_closed (stx : Syntax) : TermElabM Expr := do
  let delta ← elabDeltaHelper_closed stx
  mkAppM ``SDelta.reverse #[delta]

partial def elabGamma (stx : Syntax) : TermElabM Expr := do
  let gamma ← elabGammaHelper stx
  mkAppM ``SGamma.reverse #[gamma]

partial def elabGamma_closed (stx : Syntax) : TermElabM Expr := do
  let gamma ← elabGammaHelper_closed stx
  mkAppM ``SGamma.reverse #[gamma]

-- test parser for labels
elab "phi_parse" "(" p:owl_phi ")" : term =>
    elabPhi p
