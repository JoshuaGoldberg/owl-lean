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
| latl : Owl.Lcarrier -> SLabel
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
| unpack : SExpr -> String -> String -> SExpr -> SExpr
| if_tm :
    SExpr -> SExpr -> SExpr -> SExpr
| if_c :
    SConstr -> SExpr -> SExpr -> SExpr
| sync : SExpr -> SExpr
deriving Repr

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

open Lean Elab Meta

declare_syntax_cat owl_tm
declare_syntax_cat owl_label
declare_syntax_cat owl_type
declare_syntax_cat owl_binary
declare_syntax_cat owl_constr
declare_syntax_cat owl_cond_sym

-- syntax for labels
syntax ident : owl_label
syntax "⟨" term "⟩"  : owl_label
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

def SLabel.elab (s : SLabel) (P : TCtx) : Option (Owl.label P.length) :=
  match s with
  | .var_label i =>
    match TCtx.lookup P i with
    | .none => .none
    | .some j => .some (label.var_label j)
  | .latl l => .some (label.latl l)
  | .lmeet l1 l2 =>
    match (SLabel.elab l1 P) with
    | .none => .none
    | .some l1' =>
      match (SLabel.elab l2 P) with
      | .none => .none
      | .some l2' => .some (label.lmeet l1' l2')
  | .ljoin l1 l2 =>
    match (SLabel.elab l1 P) with
    | .none => .none
    | .some l1' =>
      match (SLabel.elab l2 P) with
      | .none => .none
      | .some l2' => .some (label.ljoin l1' l2')


-- check that labels works
#eval label_parse(x ⊓ y)

-- Just define some concrete elements:
axiom bot : Lcarrier
axiom top : Lcarrier
axiom low : Lcarrier
axiom high : Lcarrier

-- Then test:
#check label_parse(⟨ bot ⟩)
#check label_parse(⟨ low ⟩)


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

def SCondSym.elab (s : SCondSym) : Option Owl.cond_sym :=
  match s with
  | .leq => .some .leq
  | .geq => .some .geq
  | .lt => .some .lt
  | .gt => .some .gt
  | .nleq => .some .nleq
  | .ngeq => .some .ngeq
  | .nlt => .some .nlt
  | .ngt => .some .ngt

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

def SConstr.elab (s : SConstr) (P : TCtx) : Option (Owl.constr P.length) :=
  match s with
  | .condition cs l1 l2 =>
    match (SCondSym.elab cs) with
    | .none => .none
    | .some cs' =>
      match (SLabel.elab l1 P) with
      | .none => .none
      | .some l1' =>
        match (SLabel.elab l2 P) with
        | .none => .none
        | .some l2' => .some (.condition cs' l1' l2')

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

def SBinary.elab (s : SBinary) : Option Owl.binary :=
  match s with
  | .bend => .some .bend
  | .bzero b =>
      match (SBinary.elab b) with
      | .none => .none
      | .some b' => .some (.bzero b')
  | .bone b =>
      match (SBinary.elab b) with
      | .none => .none
      | .some b' => .some (.bone b')

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
syntax owl_type "*" owl_type : owl_type
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
  | `(owl_type| if $c:owl_constr then $t1:owl_type else $t2:owl_type) => do
    let elab_t1 <- elabType t1
    let elab_t2 <- elabType t2
    let elab_c <- elabConstr c
    mkAppM ``STy.t_if #[elab_c, elab_t1, elab_t2]
  | _ => throwUnsupportedSyntax

def STy.elab (s : STy) (P : TCtx) (D : TCtx): Option (Owl.ty P.length D.length) :=
  match s with
  | .var_ty i =>
    match TCtx.lookup D i with
    | .none => .none
    | .some j => .some (ty.var_ty j)
  | .Any => .some ty.Any
  | .Unit => .some ty.Unit
  | .Data l =>
      match (SLabel.elab l P) with
      | .none => .none
      | .some l' => .some (ty.Data l')
  | .Ref t =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (ty.Ref t')
  | .arr t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.arr t1' t2')
  | .prod t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.prod t1' t2')
  | .sum t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P D) with
          | .none => .none
          | .some t2' => .some (ty.sum t1' t2')
  | .all a t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P (a::D)) with
          | .none => .none
          | .some t2' => .some (ty.all t1' t2')
  | .ex a t1 t2 =>
      match (STy.elab t1 P D) with
      | .none => .none
      | .some t1' =>
          match (STy.elab t2 P (a::D)) with
          | .none => .none
          | .some t2' => .some (ty.ex t1' t2')
  | .all_l s c l t =>
      match (SCondSym.elab c) with
      | .none => .none
      | .some c' =>
          match (SLabel.elab l P) with
          | .none => .none
          | .some l'=>
              match (STy.elab t (s::P) D) with
              | .none => .none
              | .some t' => .some (ty.all_l c' l' t')
  | .t_if c t1 t2 =>
      match (SConstr.elab c P) with
      | .none => .none
      | .some c' =>
        match (STy.elab t1 P D) with
        | .none => .none
        | .some t1' =>
            match (STy.elab t2 P D) with
            | .none => .none
            | .some t2' => .some (ty.t_if c' t1' t2')

-- test parser for types
elab "type_parse" "(" p:owl_type ")" : term =>
    elabType p

-- check that types works
#eval type_parse(Unit -> Unit)
#eval type_parse(∀ t <: Any . (t -> t))

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
syntax "pack" owl_tm : owl_tm
syntax "unpack" owl_tm "as" "(" ident "," ident ")" "in" owl_tm : owl_tm
syntax "if" owl_tm "then" owl_tm "else" owl_tm : owl_tm
syntax "if" owl_constr "then" owl_tm "else" owl_tm : owl_tm
syntax "sync" owl_tm : owl_tm
syntax "let" ident "=" owl_tm "in" owl_tm : owl_tm

partial def elabTm : Syntax → MetaM Expr
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
  | `(owl_tm| pack $e:owl_tm) => do
    let elab_e <- elabTm e
    mkAppM ``SExpr.pack #[elab_e]
  | `(owl_tm| if $e1:owl_tm then $e2:owl_tm else $e3:owl_tm) => do
    let elab_e1 <- elabTm e1
    let elab_e2 <- elabTm e2
    let elab_e3 <- elabTm e3
    mkAppM ``SExpr.if_tm #[elab_e1, elab_e2, elab_e3]
  | `(owl_tm| if $c:owl_constr then $e1:owl_tm else $e2:owl_tm) => do
    let elab_c <- elabConstr c
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
  | _ => throwUnsupportedSyntax

def SExpr.elab (s : SExpr) (P : TCtx) (D : TCtx) (G : TCtx): Option (Owl.tm P.length D.length G.length) :=
  match s with
  | .var_tm i =>
    match TCtx.lookup G i with
    | .none => .none
    | .some j => .some (tm.var_tm j)
  | .error => .some tm.error
  | .skip => .some tm.skip
  | .bitstring b =>
    match (SBinary.elab b) with
    | .none => .none
    | .some b' => .some (tm.bitstring b')
  | .loc n => .some (tm.loc n)
  | .fixlam f x e =>
    match (SExpr.elab e P D (f::x::G)) with
    | .none => .none
    | .some e' => .some (tm.fixlam e')
  | .tlam t e =>
    match (SExpr.elab e P (t::D) G) with
    | .none => .none
    | .some e' => .some (tm.tlam e')
  | .l_lam l e =>
    match (SExpr.elab e (l::P) D G) with
    | .none => .none
    | .some e' => .some (tm.l_lam e')
  | .Op op e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.Op op e1' e2')
  | .zero e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.zero e')
  | .app e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.app e1' e2')
  | .alloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.alloc e')
  | .dealloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.dealloc e')
  | .assign e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.assign e1' e2')
  | .tm_pair e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tm.tm_pair e1' e2')
  | .left_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.left_tm e')
  | .right_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.right_tm e')
  | .inl e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.inl e')
  | .inr e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.inr e')
  | .case e x1 e1 x2 e2 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P D (x1::G)) with
      | .none => .none
      | .some e1' =>
        match (SExpr.elab e2 P D (x2::G)) with
        | .none => .none
        | .some e2' => .some (tm.case e' e1' e2')
  | .tapp e t =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (tm.tapp e' t')
  | .lapp e l =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SLabel.elab l P) with
      | .none => .none
      | .some l' => .some (tm.lapp e' l')
  | .pack e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.pack e')
  | .unpack e a x e1 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P (a::D) (x::G)) with
      | .none => .none
      | .some e1' => .some (tm.unpack e' e1')
  | .if_tm e1 e2 e3 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SExpr.elab e3 P D G) with
        | .none => .none
        | .some e3' => .some (tm.if_tm e1' e2' e3')
  | .if_c c e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SConstr.elab c P) with
        | .none => .none
        | .some c' => .some (tm.if_c c' e1' e2')
  | .sync e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tm.sync e')

-- test parser for terms
elab "term_parse" "(" p:owl_tm ")" : term =>
    elabTm p

-- test operator
def coin_flip : op :=
  fun (x1 x2 : binary) =>
    Dist.ret (binary.bend)

-- check that terms works
#eval term_parse(case 5 in x1 => pack x1 | x2 => (Λ t . * [[ t ]]))
#eval term_parse(* [[[ z ⊔ y ]]])
#eval term_parse(⟨ coin_flip ⟩ ( ["110"] , ["110"]))

-- check that terms works
elab "Owl_Parse" "{" p:owl_tm "}" : term => do
    elabTm p

def elabHelper (s : SExpr) : tm 0 0 0 :=
  match SExpr.elab s [] [] [] with
  | .some e => e
  | .none => tm.skip --dummy value

elab "Owl" "{" p:owl_tm "}" : term => do
  let sexprTerm : Expr <- elabTm p
  let sVal : SExpr <-
    (unsafe do
      Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm)
  match SExpr.elab sVal [] [] [] with
  | .none =>
      throwError "owl: ill-formed term"
  | .some _ => mkAppM ``elabHelper #[sexprTerm]


#eval Owl_Parse {
  unpack p as (a, x) in
    case π1 x in
      x => ⟨ ı1 x , π2 x ⟩
    | y => ⟨ ı2 y , π2 x ⟩
}

#eval Owl_Parse {
  ( fix loop ( state )
    case (! state) in
      cont => loop [ alloc cont ]
    | done => *
  ) [ alloc ⟨ ı1 * , * ⟩ ]
}

-- non functional
def sub_op : op :=
  fun (x1 x2 : binary) =>
    Dist.ret (binary.bend)

-- non functional
def mul_op : op :=
  fun (x1 x2 : binary) =>
    Dist.ret (binary.bend)

#eval Owl_Parse {
  fix factorial ( n )
    if n then
      ⟨ mul_op ⟩ ( n , factorial [ ⟨ sub_op ⟩ ( n , 1 ) ] )
    else
      1
}

-- real evaluations here
#eval Owl {
  *
}

#eval Owl {
  fix factorial ( n )
    if n then
      ⟨ mul_op ⟩ ( n , factorial [ ⟨ sub_op ⟩ ( n , 1 ) ] )
    else
      1
}

#eval Owl {
  ( fix loop ( state )
    case (! state) in
      cont => loop [ alloc cont ]
    | done => *
  ) [ alloc ⟨ ı1 * , * ⟩ ]
}

#eval Owl {
  unpack (pack 5) as (a, x) in
    case π1 x in
      x => ⟨ ı1 x , π2 x ⟩
    | y => ⟨ ı2 y , π2 x ⟩
}

#eval Owl {
  let x = 5 in
    x [x]
}
