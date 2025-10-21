import OwlLean.TypeChecker.OwlSExpr
import Lean
import Std.Data.HashMap

open Lean Elab Meta

declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_binary
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

-- syntax for labels
syntax ident : owl_label
syntax "⟨" term "⟩"  : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "$" term : owl_label
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
  | `(owl_label| $ $l:term) => do
    let l' ← Term.TermElabM.run' do
        Term.elabTerm l (mkConst ``Owl.label)
    mkAppM ``SLabel.embedlabel #[l']
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

-- syntax for types
syntax "(" owl_type ")" : owl_type
syntax ident : owl_type
syntax "Any" : owl_type
syntax "Unit" : owl_type
syntax "Data" owl_label : owl_type
syntax "Ref" owl_type : owl_type
syntax owl_type "->" owl_type : owl_type
syntax owl_type "*" owl_type : owl_type
syntax owl_type "+" owl_type : owl_type
syntax "∀" owl_type "<:" owl_type "." owl_type : owl_type
syntax "∃" owl_type "<:" owl_type "." owl_type : owl_type
syntax "∀" owl_label owl_cond_sym owl_label "." owl_type : owl_type
syntax "corr" "(" owl_label ")" "?" owl_type ":" owl_type : owl_type
syntax "Public" : owl_type
syntax "$" term : owl_type

partial def elabType : Syntax → MetaM Expr
  | `(owl_type| ( $e:owl_type)) => elabType e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| Unit) => mkAppM ``STy.Unit #[]
  | `(owl_type| Public) => mkAppM ``STy.Public #[]
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
  | `(owl_type| $t1:owl_type * $t2:owl_type) => do
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
  | `(owl_type| corr ( $c:owl_label ) ? $t1:owl_type : $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    let elab_c <- elabLabel c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | `(owl_type| $ $t:term) => do
    let t' ← Term.TermElabM.run' do
        Term.elabTerm t (mkConst ``Owl.ty)
    mkAppM ``STy.embedty #[t']
  | _ => throwUnsupportedSyntax

-- syntax for terms
syntax "(" owl_tm ")" : owl_tm
syntax ident : owl_tm
syntax num : owl_tm
syntax "error" : owl_tm
syntax "*" : owl_tm
syntax "[" owl_binary "]" : owl_tm
syntax "fix" ident "(" ident ")" owl_tm : owl_tm
syntax "Λ" owl_type "." owl_tm : owl_tm
syntax "Λβ" owl_label "." owl_tm : owl_tm
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
syntax "case" owl_tm "in" owl_tm "=>" owl_tm "|" owl_tm "=>" owl_tm : owl_tm
syntax owl_tm "[[" owl_type "]]" : owl_tm
syntax owl_tm "[[[" owl_label "]]]" : owl_tm
syntax "pack" "(" owl_type "," owl_tm ")" : owl_tm
syntax "unpack" owl_tm "as" "(" ident "," ident ")" "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" "corr" "(" owl_label ")" "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm
syntax "let" ident "=" owl_tm "in" owl_tm : owl_tm
syntax "λ" "(" ident ":" owl_type ")" ":" owl_type "=>" owl_tm : owl_tm
syntax "λ" ident "=>" owl_tm : owl_tm
syntax "$" term : owl_tm
syntax "corr_case" owl_label "in" owl_tm : owl_tm
syntax "(" owl_tm ":" owl_type ")" : owl_tm

-- ALLOW : let (x , y) = e in ...
-- expands to :
-- let e' = e in
-- let x = π1 e' in
-- let y = π2 e' in ...

partial def elabTm : Syntax → TermElabM Expr
  | `(owl_tm| ( $e:owl_tm)) => elabTm e
  | `(owl_tm| $id:ident) =>
        mkAppM ``SExpr.var_tm #[mkStrLit id.getId.toString]
  | `(owl_tm| $n:num) =>
    mkAppM ``SExpr.loc #[mkNatLit n.getNat]
  | `(owl_tm| error) => mkAppM ``SExpr.error #[]
  | `(owl_tm| *) => mkAppM ``SExpr.skip #[]
  | `(owl_tm| [ $b:owl_binary ] ) => do
    let elab_b <- elabBinary b
    mkAppM ``SExpr.bitstring #[elab_b]
  | `(owl_tm| fix $f:ident ( $id:ident ) $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.fixlam #[mkStrLit f.getId.toString, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.tlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λβ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.l_lam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.tm_pair #[elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let t' ← Term.TermElabM.run' do
        Term.elabTerm t (mkConst ``Owl.op)
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.Op #[t', elab_e1, elab_e2]
  | `(owl_tm| $ $t:term) => do
    let t' ← Term.TermElabM.run' do
        Term.elabTerm t (mkConst ``Owl.tm)
    mkAppM ``SExpr.embedtm #[t']
  | `(owl_tm| zero $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.zero #[elab_e]
  | `(owl_tm| $e1:owl_tm [ $e2:owl_tm ]) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.app #[elab_e1, elab_e2]
  | `(owl_tm| alloc $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.alloc #[elab_e]
  | `(owl_tm| ! $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.dealloc #[elab_e]
  | `(owl_tm| $e1:owl_tm := $e2:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.assign #[elab_e1, elab_e2]
  | `(owl_tm| π1 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.left_tm #[elab_e]
  | `(owl_tm| π2 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.right_tm #[elab_e]
  | `(owl_tm| ı1 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.inl #[elab_e]
  | `(owl_tm| ı2 $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.inr #[elab_e]
  | `(owl_tm| case $e1:owl_tm in $id1:ident => $e2:owl_tm | $id2:ident => $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExpr.case #[elab_e1, mkStrLit id1.getId.toString, elab_e2, mkStrLit id2.getId.toString, elab_e3]
  | `(owl_tm| $e:owl_tm [[ $t:owl_type ]]) => do
    let elab_e <- elabTm e
    let elab_t <- elabType t
    mkAppM ``SExpr.tapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [[[ $l:owl_label ]]]) => do
    let elab_e <- elabTm e
    let elab_l <- elabLabel l
    mkAppM ``SExpr.lapp #[elab_e, elab_l]
  | `(owl_tm| unpack $e1:owl_tm as ($id1:ident, $id2:ident) in $e2:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.unpack #[elab_e1, mkStrLit id1.getId.toString, mkStrLit id2.getId.toString, elab_e2]
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let elab_t <- elabType t
    let elab_e <- elabTm e
    mkAppM ``SExpr.pack #[elab_t, elab_e]
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExpr.if_tm #[elab_e1, elab_e2, elab_e3]
  | `(owl_tm| if corr($c:owl_label) then $e1:owl_tm else $e2:owl_tm) => do
    let elab_c <- elabLabel c
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExpr.if_c #[elab_c, elab_e1, elab_e2]
  | `(owl_tm| sync $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.sync #[elab_e]
  | `(owl_tm| let $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let elab_e <- elabTm e
    let elab_b <- elabTm b
    let unused := "unused variable"
    let lambda <- mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id1.getId.toString, elab_b]
    mkAppM ``SExpr.app #[lambda, elab_e]
  | `(owl_tm| λ ($id:ident : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    let elab_e <- elabTm e
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    let unused := "unused variable"
    let lambda <- mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
    let arr <- mkAppM ``STy.arr #[elab_t1, elab_t2]
    mkAppM ``SExpr.annot #[lambda, arr]
  | `(owl_tm| λ $id:ident => $e:owl_tm) => do
    let elab_e <- elabTm e
    let unused := "unused variable"
    mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| corr_case $l1:owl_label in $e:owl_tm ) => do
    let elab_e <- elabTm e
    let elab_l1 <- elabLabel l1
    mkAppM ``SExpr.corr_case #[elab_l1, elab_e]
  | `(owl_tm| ( $e:owl_tm : $t:owl_type)) => do
    let elab_e <- elabTm e
    let elab_t <- elabType t
    mkAppM ``SExpr.annot #[elab_e, elab_t]
  | _ => throwUnsupportedSyntax

-- CLOSED ELABORATORS

partial def elabLabel_closed : Syntax → MetaM Expr
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
  | `(owl_label| $ $_:term) => mkAppM ``SLabel.default #[]
  | _ => throwUnsupportedSyntax

partial def elabConstr_closed : Syntax → MetaM Expr
  | `(owl_constr| ( $e:owl_constr)) => elabConstr_closed e
  | `(owl_constr| $l1:owl_label $c:owl_cond_sym $l2:owl_label) => do
      let elab_l1 <- elabLabel_closed l1
      let elab_l2 <- elabLabel_closed l2
      let elab_c <- elabCondSym c
      mkAppM ``SConstr.condition #[elab_c, elab_l1, elab_l2]
  | _ => throwUnsupportedSyntax

partial def elabType_closed : Syntax → MetaM Expr
  | `(owl_type| ( $e:owl_type)) => elabType_closed e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| Unit) => mkAppM ``STy.Unit #[]
  | `(owl_type| Public) => mkAppM ``STy.Public #[]
  | `(owl_type| Data $l:owl_label) => do
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
  | `(owl_type| corr ( $c:owl_label ) ? $t1:owl_type : $t2:owl_type) => do
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    let elab_c <- elabLabel_closed c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | `(owl_type| $ $_:term) => mkAppM ``STy.default #[]
  | _ => throwUnsupportedSyntax

partial def elabTm_closed : Syntax → TermElabM Expr
  | `(owl_tm| ( $e:owl_tm)) => elabTm_closed e
  | `(owl_tm| $id:ident) =>
        mkAppM ``SExpr.var_tm #[mkStrLit id.getId.toString]
  | `(owl_tm| $n:num) =>
    mkAppM ``SExpr.loc #[mkNatLit n.getNat]
  | `(owl_tm| error) => mkAppM ``SExpr.error #[]
  | `(owl_tm| *) => mkAppM ``SExpr.skip #[]
  | `(owl_tm| [ $b:owl_binary ] ) => do
    let elab_b <- elabBinary b
    mkAppM ``SExpr.bitstring #[elab_b]
  | `(owl_tm| fix $f:ident ( $id:ident ) $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.fixlam #[mkStrLit f.getId.toString, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.tlam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| Λβ $id:ident . $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.l_lam #[mkStrLit id.getId.toString, elab_e]
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.tm_pair #[elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let t' ← Term.TermElabM.run' do
        Term.elabTerm t (mkConst ``Owl.op)
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.Op #[t', elab_e1, elab_e2]
  | `(owl_tm| $ $_:term) => mkAppM ``SExpr.default #[]
  | `(owl_tm| zero $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.zero #[elab_e]
  | `(owl_tm| $e1:owl_tm [ $e2:owl_tm ]) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.app #[elab_e1, elab_e2]
  | `(owl_tm| alloc $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.alloc #[elab_e]
  | `(owl_tm| ! $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.dealloc #[elab_e]
  | `(owl_tm| $e1:owl_tm := $e2:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.assign #[elab_e1, elab_e2]
  | `(owl_tm| π1 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.left_tm #[elab_e]
  | `(owl_tm| π2 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.right_tm #[elab_e]
  | `(owl_tm| ı1 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.inl #[elab_e]
  | `(owl_tm| ı2 $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.inr #[elab_e]
  | `(owl_tm| case $e1:owl_tm in $id1:ident => $e2:owl_tm | $id2:ident => $e3:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    let elab_e3 <- elabTm_closed e3
    mkAppM ``SExpr.case #[elab_e1, mkStrLit id1.getId.toString, elab_e2, mkStrLit id2.getId.toString, elab_e3]
  | `(owl_tm| $e:owl_tm [[ $t:owl_type ]]) => do
    let elab_e <- elabTm_closed e
    let elab_t <- elabType_closed t
    mkAppM ``SExpr.tapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm [[[ $l:owl_label ]]]) => do
    let elab_e <- elabTm_closed e
    let elab_l <- elabLabel l
    mkAppM ``SExpr.lapp #[elab_e, elab_l]
  | `(owl_tm| unpack $e1:owl_tm as ($id1:ident, $id2:ident) in $e2:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.unpack #[elab_e1, mkStrLit id1.getId.toString, mkStrLit id2.getId.toString, elab_e2]
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let elab_t <- elabType_closed t
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.pack #[elab_t, elab_e]
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    let elab_e3 <- elabTm_closed e3
    mkAppM ``SExpr.if_tm #[elab_e1, elab_e2, elab_e3]
  | `(owl_tm| if corr($c:owl_label) then $e1:owl_tm else $e2:owl_tm) => do
    let elab_c <- elabLabel_closed c
    let elab_e1 <- elabTm_closed e1
    let elab_e2 <- elabTm_closed e2
    mkAppM ``SExpr.if_c #[elab_c, elab_e1, elab_e2]
  | `(owl_tm| sync $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    mkAppM ``SExpr.sync #[elab_e]
  | `(owl_tm| let $id1:ident = $e:owl_tm  in $b:owl_tm) => do
    let elab_e <- elabTm_closed e
    let elab_b <- elabTm_closed b
    let unused := "unused variable"
    let lambda <- mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id1.getId.toString, elab_b]
    mkAppM ``SExpr.app #[lambda, elab_e]
  | `(owl_tm| λ ($id:ident : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    let elab_t1 <- elabType_closed t1
    let elab_t2 <- elabType_closed t2
    let unused := "unused variable"
    let lambda <- mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
    let arr <- mkAppM ``STy.arr #[elab_t1, elab_t2]
    mkAppM ``SExpr.annot #[lambda, arr]
  | `(owl_tm| λ $id:ident => $e:owl_tm) => do
    let elab_e <- elabTm_closed e
    let unused := "unused variable"
    mkAppM ``SExpr.fixlam #[mkStrLit unused, mkStrLit id.getId.toString, elab_e]
  | `(owl_tm| corr_case $l1:owl_label in $e:owl_tm ) => do
    let elab_e <- elabTm_closed e
    let elab_l1 <- elabLabel_closed l1
    mkAppM ``SExpr.corr_case #[elab_l1, elab_e]
  | `(owl_tm| ( $e:owl_tm : $t:owl_type)) => do
    let elab_e <- elabTm_closed e
    let elab_t <- elabType_closed t
    mkAppM ``SExpr.annot #[elab_e, elab_t]
  | _ => throwUnsupportedSyntax

-- Phi Mappings
syntax "(" owl_phi_entry ")" : owl_phi_entry
syntax  ident owl_cond_sym owl_label : owl_phi_entry
syntax ident : owl_phi_entry

partial def elabPhiEntry : Syntax → MetaM Expr
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

partial def elabPhiEntry_closed : Syntax → MetaM Expr
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

partial def elabDeltaEntry : Syntax → MetaM Expr
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaEntry e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let elab_t <- elabType t
      mkAppM ``SDeltaEntry.DeltaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

partial def elabDeltaEntry_closed : Syntax → MetaM Expr
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaEntry_closed e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let elab_t <- elabType_closed t
      mkAppM ``SDeltaEntry.DeltaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

syntax "(" owl_gamma_entry ")" : owl_gamma_entry
syntax  ident "=>" owl_type : owl_gamma_entry

partial def elabGammaEntry : Syntax → MetaM Expr
  | `(owl_gamma_entry| ( $e:owl_gamma_entry)) => elabGammaEntry e
  | `(owl_gamma_entry|  $id:ident => $t:owl_type) => do
      let elab_t <- elabType t
      mkAppM ``SGammaEntry.GammaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

partial def elabGammaEntry_closed : Syntax → MetaM Expr
  | `(owl_gamma_entry| ( $e:owl_gamma_entry)) => elabGammaEntry_closed e
  | `(owl_gamma_entry|  $id:ident => $t:owl_type) => do
      let elab_t <- elabType_closed t
      mkAppM ``SGammaEntry.GammaEntry #[mkStrLit id.getId.toString, elab_t]
  | _ => throwUnsupportedSyntax

syntax "(" owl_psi_entry ")" : owl_psi_entry
syntax  "corr(" owl_label ")" : owl_psi_entry
syntax  "¬corr(" owl_label ")" : owl_psi_entry

partial def elabPsiEntry : Syntax → MetaM Expr
  | `(owl_psi_entry| ( $e:owl_psi_entry)) => elabPsiEntry e
  | `(owl_psi_entry| corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel l1
      mkAppM ``SPsiEntry.PsiCorr #[elab_l1]
      | `(owl_psi_entry| ¬corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel l1
      mkAppM ``SPsiEntry.PsiNotCorr #[elab_l1]
  | _ => throwUnsupportedSyntax

partial def elabPsiEntry_closed : Syntax → MetaM Expr
  | `(owl_psi_entry| ( $e:owl_psi_entry)) => elabPsiEntry_closed e
  | `(owl_psi_entry| corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel_closed l1
      mkAppM ``SPsiEntry.PsiCorr #[elab_l1]
      | `(owl_psi_entry| ¬corr($l1:owl_label)) => do
      let elab_l1 <- elabLabel_closed l1
      mkAppM ``SPsiEntry.PsiNotCorr #[elab_l1]
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

partial def elabPhiHelper : Syntax → MetaM Expr
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

partial def elabPhiHelper_closed : Syntax → MetaM Expr
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

partial def elabDeltaHelper : Syntax → MetaM Expr
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

partial def elabDeltaHelper_closed : Syntax → MetaM Expr
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

partial def elabGammaHelper : Syntax → MetaM Expr
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

partial def elabGammaHelper_closed : Syntax → MetaM Expr
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

partial def elabPsi : Syntax → MetaM Expr
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

partial def elabPsi_closed : Syntax → MetaM Expr
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

partial def elabPhi (stx : Syntax) : MetaM Expr := do
  let phi ← elabPhiHelper stx
  mkAppM ``SPhi.reverse #[phi]

partial def elabPhi_closed (stx : Syntax) : MetaM Expr := do
  let phi ← elabPhiHelper_closed stx
  mkAppM ``SPhi.reverse #[phi]

partial def elabDelta (stx : Syntax) : MetaM Expr := do
  let delta ← elabDeltaHelper stx
  mkAppM ``SDelta.reverse #[delta]

partial def elabDelta_closed (stx : Syntax) : MetaM Expr := do
  let delta ← elabDeltaHelper_closed stx
  mkAppM ``SDelta.reverse #[delta]

partial def elabGamma (stx : Syntax) : MetaM Expr := do
  let gamma ← elabGammaHelper stx
  mkAppM ``SGamma.reverse #[gamma]

partial def elabGamma_closed (stx : Syntax) : MetaM Expr := do
  let gamma ← elabGammaHelper_closed stx
  mkAppM ``SGamma.reverse #[gamma]

-- test parser for labels
elab "phi_parse" "(" p:owl_phi ")" : term =>
    elabPhi p

#reduce phi_parse ( (x, y, z ⊑ y) )
