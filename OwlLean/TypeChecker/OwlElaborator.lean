import OwlLean.TypeChecker.OwlSExpr
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.TcSimple

open Lean Elab Meta

deriving instance ToExpr for SLabel
deriving instance ToExpr for SCondSym
deriving instance ToExpr for STy

declare_syntax_cat owl_var
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

-- syntax for variables
syntax ident : owl_var
syntax "_" : owl_var

-- syntax for labels
syntax ident : owl_label
syntax "⟨" term "⟩"  : owl_label
syntax owl_label "⊔" owl_label : owl_label
syntax owl_label "⊓" owl_label : owl_label
syntax "$" term:max "[" owl_label,* "]" : owl_label
syntax "$" term:max : owl_label
syntax "(" owl_label ")" : owl_label

partial def elabVar : Syntax → String
  | `(owl_var| $id:ident) => id.getId.toString
  | _ => "unused variable"

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

-- syntax for binary
syntax str : owl_binary

partial def buildSBinaryExpr (chars : List Char) : TermElabM Expr :=
  match chars with
  | [] => return mkConst ``SBinary.bend
  | '0' :: rest => do
    let restExpr <- buildSBinaryExpr rest
    mkAppM ``SBinary.bzero #[restExpr]
  | '1' :: rest => do
    let restExpr <- buildSBinaryExpr rest
    mkAppM ``SBinary.bone #[restExpr]
  | _ :: _ => throwError "Invalid binary character"

partial def elabBinary : Syntax → TermElabM Expr
  | `(owl_binary| $val:str) => buildSBinaryExpr val.getString.data
  | _ => throwUnsupportedSyntax

-- syntax for types
syntax "(" owl_type ")" : owl_type
syntax ident : owl_type
syntax "Any" : owl_type
syntax "unit" : owl_type
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
syntax "$" term:max "[" owl_label,* "]" "[" owl_type,* "]" : owl_type

partial def elabType : Syntax → TermElabM Expr
  | `(owl_type| ( $e:owl_type)) => elabType e
  | `(owl_type| $id:ident) =>
        mkAppM ``STy.var_ty #[mkStrLit id.getId.toString]
  | `(owl_type| Any) => mkAppM ``STy.Any #[]
  | `(owl_type| unit) => mkAppM ``STy.Unit #[]
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
  | `(owl_type| $ $t:term [ $ls:owl_label,* ] [ $ts:owl_type,* ]) => do
    let ls' <- ls.getElems.mapM elabLabel
    let ts' <- ts.getElems.mapM elabType
    let ls_list <- mkListLit (mkConst ``SLabel) ls'.toList
    let ts_list <- mkListLit (mkConst ``STy) ts'.toList
    let t' ← Term.elabTerm t (mkConst ``Owl.ty)
    mkAppM ``STy.embedty #[t', ls_list, ts_list]
  | _ => throwUnsupportedSyntax

notation:100 "PURE" => pure ()
notation:100 "THROW" => throw ()

-- syntax for terms
syntax "(" owl_tm ")" : owl_tm
syntax ident : owl_tm
syntax num : owl_tm
syntax "error" : owl_tm
syntax "()" : owl_tm
syntax owl_binary : owl_tm
syntax "fix" owl_var "(" owl_var ")" owl_tm : owl_tm
syntax "Λ" owl_var "." owl_tm : owl_tm
syntax "Λβ" owl_var "." owl_tm : owl_tm
syntax "⟨" owl_tm "," owl_tm "⟩" : owl_tm
syntax "⟨" term "⟩" "(" owl_tm "," owl_tm ")" : owl_tm -- Binary Op case
syntax "⟨" term "⟩" "(" owl_tm ")" : owl_tm -- Unary Op case
syntax "zero" owl_tm : owl_tm
syntax owl_tm owl_tm : owl_tm
syntax "alloc" owl_tm : owl_tm
syntax "!" owl_tm : owl_tm
syntax owl_tm ":=" owl_tm : owl_tm
syntax "π1" owl_tm : owl_tm
syntax "π2" owl_tm : owl_tm
syntax "ı1" owl_tm : owl_tm
syntax "ı2" owl_tm : owl_tm
syntax "case" owl_tm "in" "|" "inl" owl_var "=>" owl_tm "|" "inr" owl_var "=>" owl_tm : owl_tm
syntax owl_tm "[" owl_type "]" : owl_tm
syntax owl_tm "⟨" owl_label "⟩" : owl_tm
syntax "pack" "(" owl_type "," owl_tm ")" : owl_tm
syntax "unpack" owl_tm "as" "(" owl_var "," owl_var ")" "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" "corr" "(" owl_label ")" "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm
syntax "let" owl_var "=" owl_tm "in" owl_tm : owl_tm
syntax owl_tm ";" owl_tm : owl_tm
syntax "let" owl_var ":" owl_type "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" owl_var "," owl_var ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "let" "(" owl_var "," owl_var "," owl_var ")" "=" owl_tm "in" owl_tm : owl_tm
syntax "λ" "(" owl_var ":" owl_type ")" ":" owl_type "=>" owl_tm : owl_tm
syntax "λ" owl_var "=>" owl_tm : owl_tm
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
  | `(owl_tm| $b:owl_binary ) => do
    let elab_b <- elabBinary b
    mkAppM ``SExprX.bitstring #[elab_b]
  | `(owl_tm| fix $f:owl_var ( $v:owl_var ) $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.fixlam #[mkStrLit (elabVar f), mkStrLit (elabVar v), elab_e]
  | `(owl_tm| Λ $v:owl_var . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.tlam #[mkStrLit (elabVar v), elab_e]
  | `(owl_tm| Λβ $v:owl_var . $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.l_lam #[mkStrLit (elabVar v), elab_e]
  | `(owl_tm|⟨ $e1:owl_tm , $e2:owl_tm ⟩) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.tm_pair #[elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm , $e2:owl_tm )) => do
    let t' ← Term.elabTerm t (mkConst ``String)
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.Op #[t', elab_e1, elab_e2]
  | `(owl_tm| ⟨ $t:term ⟩ ( $e1:owl_tm )) => do
    let t' ← Term.elabTerm t (mkConst ``String)
    let elab_e1 <- elabTm e1
    let bend ← mkAppM ``SBinary.bend #[]
    let arbitrary_bit_x <- mkAppM ``SExprX.bitstring #[bend]
    let se <- mkEmptySyntax "arbitrary"
    let arbitrary_bit <- mkAppM ``SExpr.mk #[se, arbitrary_bit_x]
    mkAppM ``SExprX.Op #[t', elab_e1, arbitrary_bit]
  | `(owl_tm| $ $t:term [ $ls:owl_label,* ] [ $ts:owl_type,* ] [ $es:owl_tm,* ]) => do
    let ls' <- ls.getElems.mapM elabLabel
    let ts' <- ts.getElems.mapM elabType
    let es' <- es.getElems.mapM elabTm
    let ls_list <- mkListLit (mkConst ``SLabel) ls'.toList
    let ts_list <- mkListLit (mkConst ``STy) ts'.toList
    let es_list <- mkListLit (mkConst ``SExpr) es'.toList
    let t' ← Term.elabTerm t (mkConst ``Owl.tm)
    mkAppM ``SExprX.embedtm #[t', ls_list, ts_list, es_list]
  | `(owl_tm| zero $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExprX.zero #[elab_e]
  | `(owl_tm| $e1:owl_tm $e2:owl_tm) => do
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
  | `(owl_tm| case $e1:owl_tm in | inl $v1:owl_var => $e2:owl_tm | inr $v2:owl_var => $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExprX.case #[elab_e1, mkStrLit (elabVar v1), elab_e2, mkStrLit (elabVar v2), elab_e3]
  | `(owl_tm| $e:owl_tm [ $t:owl_type ]) => do
    let elab_e <- elabTm e
    let elab_t <- elabType t
    mkAppM ``SExprX.tapp #[elab_e, elab_t]
  | `(owl_tm| $e:owl_tm ⟨ $l:owl_label ⟩) => do
    let elab_e <- elabTm e
    let elab_l <- elabLabel l
    mkAppM ``SExprX.lapp #[elab_e, elab_l]
  | `(owl_tm| unpack $e1:owl_tm as ($v1:owl_var, $v2:owl_var) in $e2:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    mkAppM ``SExprX.unpack #[elab_e1, mkStrLit (elabVar v1), mkStrLit (elabVar v2), elab_e2]
  | `(owl_tm| pack ($t:owl_type, $e:owl_tm)) => do
    let elab_t <- elabType t
    let elab_e <- elabTm e
    mkAppM ``SExprX.pack #[elab_t, elab_e]
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
  | `(owl_tm| let $v1:owl_var = $e:owl_tm  in $b:owl_tm) => do
    let elab_e <- elabTm e
    let elab_b <- elabTm b
    mkAppM ``SExprX.elet #[mkStrLit (elabVar v1), elab_e, elab_b]
  | `(owl_tm| let $v1:owl_var : $t:owl_type = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm |
      let $v1 = ($e : $t) in $b
    ))
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm| let $v1 = π1 $e in let $v2 = π2 $e in $b))
  | `(owl_tm| let ($v1:owl_var, $v2:owl_var, $v3:owl_var) = $e:owl_tm  in $b:owl_tm) => do
    elabTmX (<- `(owl_tm |
      let $v1 = π1 $e in
      let $v2 = π1 (π2 $e) in
      let $v3 = π2 (π2 $e) in
      $b
    ))
  | `(owl_tm| $e1:owl_tm ; $e2:owl_tm ) => do
    elabTmX (<- `(owl_tm|
      (let _ = $e1 in $e2)))
  | `(owl_tm| λ ($v:owl_var : $t1:owl_type) : $t2:owl_type => $e:owl_tm) => do
    elabTmX (<- `(owl_tm|
      ((λ $v => $e) : ($t1 -> $t2)
    )))
  | `(owl_tm| λ $v:owl_var => $e:owl_tm) => do
    let elab_e <- elabTm e
    let unused := "unused variable"
    mkAppM ``SExprX.fixlam #[mkStrLit unused, mkStrLit (elabVar v), elab_e]
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

syntax "(" owl_delta_entry ")" : owl_delta_entry
syntax  ident "<:" owl_type : owl_delta_entry

partial def elabDeltaEntry : Syntax → TermElabM Expr
  | `(owl_delta_entry| ( $e:owl_delta_entry)) => elabDeltaEntry e
  | `(owl_delta_entry|  $id:ident <: $t:owl_type) => do
      let elab_t <- elabType t
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

partial def elabPhi (stx : Syntax) : TermElabM Expr := do
  let phi ← elabPhiHelper stx
  mkAppM ``SPhi.reverse #[phi]

partial def elabDelta (stx : Syntax) : TermElabM Expr := do
  let delta ← elabDeltaHelper stx
  mkAppM ``SDelta.reverse #[delta]

partial def elabGamma (stx : Syntax) : TermElabM Expr := do
  let gamma ← elabGammaHelper stx
  mkAppM ``SGamma.reverse #[gamma]

-- test parser for labels
elab "phi_parse" "(" p:owl_phi ")" : term =>
    elabPhi p
