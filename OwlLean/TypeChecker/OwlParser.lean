import OwlLean.TypeChecker.OwlElaborator
import OwlLean.TypeChecker.OwlTyping
import Lean
import Std.Data.HashMap

open Owl


def TCtx := List String

@[simp]
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

-- test parser for labels
elab "label_parse" "(" p:owl_label ")" : term =>
    elabLabel p

@[simp]
def list_to_finmap : (xs : List t) → Fin xs.length → t
  | [] => Fin.elim0
  | x :: xs => cons x (list_to_finmap xs)

#print Except

@[simp]
def SLabel.elab (s : SLabel) (P : TCtx) : Except String (Owl.label P.length) :=
  match s with
  | .var_label i =>
    match TCtx.lookup P i with
    | .none => throw s!"Unknown label variable: {i} "
    | .some j => return (label.var_label j)
  | .latl l => return (label.latl l)
  | .lmeet l1 l2 => do
    let l1' <- SLabel.elab l1 P
    let l2' <- SLabel.elab l2 P
    return (label.lmeet l1' l2')
  | .ljoin l1 l2 => do
    let l1' <- SLabel.elab l1 P
    let l2' <- SLabel.elab l2 P
    return (label.ljoin l1' l2')
  | @embedlabel len l xs => do
    let elab_xs <- xs.mapM (fun x => SLabel.elab x P)
    if h : len = elab_xs.length then
      return (subst_label (list_to_finmap elab_xs) (h ▸ l))
    else throw "should not be reached"
  | .default => return label.default

@[simp]
def SCondSym.elab (s : SCondSym) : Except String Owl.cond_sym :=
  match s with
  | .leq => return .leq
  | .geq => return .geq
  | .lt => return .lt
  | .gt => return .gt
  | .nleq => return .nleq
  | .ngeq => return .ngeq
  | .nlt => return .nlt
  | .ngt => return .ngt

-- test parser for cond_sym
elab "cond_sym_parse" "(" p:owl_cond_sym ")" : term =>
    elabCondSym p

@[simp]
def SConstr.elab (s : SConstr) (P : TCtx) : Except String (Owl.constr P.length) :=
  match s with
  | .condition cs l1 l2 => do
    let cs' <- SCondSym.elab cs
    let l1' <- l1.elab P
    let l2' <- l2.elab P
    return (.condition cs' l1' l2')
-- test parser for constraints
elab "constraint_parse" "(" p:owl_constr ")" : term =>
    elabConstr p

@[simp]
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

@[simp]
def STy.elab (s : STy) (P : TCtx) (D : TCtx): Except String (Owl.ty P.length D.length) :=
  match s with
  | .var_ty i =>
    match TCtx.lookup D i with
    | .none => throw s!"Unknown variable: {i}"
    | .some j => return (ty.var_ty j)
  | .Any => return ty.Any
  | .Unit => return ty.Unit
  | .Public => return ty.Public
  | .Data l => do
    let l' ← SLabel.elab l P
    return ty.Data l'
  | .Ref t => do
    let t' ← STy.elab t P D
    return ty.Ref t'
  | .arr t1 t2 => do
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P D
    return ty.arr t1' t2'
  | .prod t1 t2 => do
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P D
    return ty.prod t1' t2'
  | .sum t1 t2 => do
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P D
    return ty.sum t1' t2'
  | .all a t1 t2 => do
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P (a :: D)
    return ty.all t1' t2'
  | .ex a t1 t2 => do
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P (a :: D)
    return ty.ex t1' t2'
  | .all_l s c l t => do
    let c' ← SCondSym.elab c
    let l' ← SLabel.elab l P
    let t' ← STy.elab t (s :: P) D
    return ty.all_l c' l' t'
  | .t_if c t1 t2 => do
    let c' ← SLabel.elab c P
    let t1' ← STy.elab t1 P D
    let t2' ← STy.elab t2 P D
    return ty.t_if c' t1' t2'
  | @embedty llen tlen t ls ts => do
    let rec go1 : List SLabel → Except String (List (label P.length))
      | [] => return []
      | x::xs => do
        let res ← SLabel.elab x P
        let rest ← go1 xs
        return (res :: rest)
    let rec go2 : List STy → Except String (List (ty P.length D.length))
      | [] => return []
      | x::xs => do
        let res ← STy.elab x P D
        let rest ← go2 xs
        return (res :: rest)
    let elab_ls ← go1 ls
    let elab_ts ← go2 ts
    if h : llen = elab_ls.length then
      if k : tlen = elab_ts.length then
        return subst_ty (list_to_finmap elab_ls) (list_to_finmap elab_ts) (k ▸ (h ▸ t))
      else
        throw s!"embedty: type argument length mismatch: expected {tlen}, got {elab_ts.length}"
    else
      throw s!"embedty: label argument length mismatch: expected {llen}, got {elab_ls.length}"
  | .default => return ty.default

-- test parser for types
elab "type_parse" "(" p:owl_type ")" : term =>
    elabType p

mutual
  @[simp]
  def SExpr.elab (s : SExpr) (P : TCtx) (D : TCtx) (G : TCtx): Except String (Owl.tm P.length D.length G.length) :=
    match s with
    | .mk stx v => do
      let v2 <- SExprX.elab v P D G
      return (.mk stx v2)

@[simp]
def SExprX.elab (s : SExprX) (P : TCtx) (D : TCtx) (G : TCtx): Except String (Owl.tmX P.length D.length G.length) :=
  match s with
  | .var_tm i =>
    match TCtx.lookup G i with
    | .none    => throw s!"SExprX.elab: var index {i} not found in context"
    | .some j  => return tmX.var_tm j
  | .error => return tmX.error
  | .skip  => return tmX.skip
  | .bitstring b =>
    match SBinary.elab b with
    | .none    => throw s!"SExprX.elab: failed to elaborate bitstring"
    | .some b' => return tmX.bitstring b'
  | .loc n => return tmX.loc n
  | .fixlam f x e => do
    let e' ← SExpr.elab e P D (f::x::G)
    return tmX.fixlam x e'
  | .tlam t e => do
    let e' ← SExpr.elab e P (t::D) G
    return tmX.tlam e'
  | .l_lam l e => do
    let e' ← SExpr.elab e (l::P) D G
    return tmX.l_lam e'
  | .Op op e1 e2 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    return tmX.Op op e1' e2'
  | @SExprX.embedtm llen tlen mlen e ls ts es => do
    let rec go1 : List SLabel → Except String (List (label P.length))
      | [] => return []
      | x::xs => do
        let res ← SLabel.elab x P
        let rest ← go1 xs
        return (res :: rest)
    let rec go2 : List STy → Except String (List (ty P.length D.length))
      | [] => return []
      | x::xs => do
        let res ← STy.elab x P D
        let rest ← go2 xs
        return (res :: rest)
    let rec go3 : List SExpr → Except String (List (tm P.length D.length G.length))
      | [] => return []
      | x::xs => do
        let res ← SExpr.elab x P D G
        let rest ← go3 xs
        return (res :: rest)
    let elab_ls ← go1 ls
    let elab_ts ← go2 ts
    let elab_es ← go3 es
    if h : llen = elab_ls.length then
      if k : tlen = elab_ts.length then
        if j : mlen = elab_es.length then
          return subst_tmX (list_to_finmap elab_ls) (list_to_finmap elab_ts) (list_to_finmap elab_es) (j ▸ (k ▸ (h ▸ e.get)))
        else throw s!"SExprX.elab: embedtm term argument length mismatch: expected {mlen}, got {elab_es.length}"
      else throw s!"SExprX.elab: embedtm type argument length mismatch: expected {tlen}, got {elab_ts.length}"
    else throw s!"SExprX.elab: embedtm label argument length mismatch: expected {llen}, got {elab_ls.length}"
  | .zero e => do
    let e' ← SExpr.elab e P D G
    return tmX.zero e'
  | .app e1 e2 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    return tmX.app e1' e2'
  | .alloc e => do
    let e' ← SExpr.elab e P D G
    return tmX.alloc e'
  | .dealloc e => do
    let e' ← SExpr.elab e P D G
    return tmX.dealloc e'
  | .assign e1 e2 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    return tmX.assign e1' e2'
  | .tm_pair e1 e2 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    return tmX.tm_pair e1' e2'
  | .left_tm e => do
    let e' ← SExpr.elab e P D G
    return tmX.left_tm e'
  | .right_tm e => do
    let e' ← SExpr.elab e P D G
    return tmX.right_tm e'
  | .inl e => do
    let e' ← SExpr.elab e P D G
    return tmX.inl e'
  | .inr e => do
    let e' ← SExpr.elab e P D G
    return tmX.inr e'
  | .case e x1 e1 x2 e2 => do
    let e' ← SExpr.elab e P D G
    let e1' ← SExpr.elab e1 P D (x1 :: G)
    let e2' ← SExpr.elab e2 P D (x2 :: G)
    return tmX.case e' e1' e2'
  | .tapp e t => do
    let e' ← SExpr.elab e P D G
    let t' ← STy.elab t P D
    return tmX.tapp e' t'
  | .lapp e l => do
    let e' ← SExpr.elab e P D G
    let l' ← SLabel.elab l P
    return tmX.lapp e' l'
  | .pack t e => do
    let e' ← SExpr.elab e P D G
    let t' ← STy.elab t P D
    return tmX.pack t' e'
  | .unpack e a x e1 => do
    let e' ← SExpr.elab e P D G
    let e1' ← SExpr.elab e1 P (a::D) (x::G)
    return tmX.unpack e' e1'
  | .if_tm e1 e2 e3 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    let e3' ← SExpr.elab e3 P D G
    return tmX.if_tm e1' e2' e3'
  | .if_c c e1 e2 => do
    let e1' ← SExpr.elab e1 P D G
    let e2' ← SExpr.elab e2 P D G
    let c'  ← SLabel.elab c P
    return tmX.if_c c' e1' e2'
  | .sync e => do
    let e' ← SExpr.elab e P D G
    return tmX.sync e'
  | .corr_case lab e => do
    let e' ← SExpr.elab e P D G
    let lab' ← SLabel.elab lab P
    return tmX.corr_case lab' e'
  | .annot e t => do
    let e' ← SExpr.elab e P D G
    let t' ← STy.elab t P D
    return tmX.annot e' t'
  | .default => return tmX.default
  | .elet s e1 e2 => do
    let arg ← SExpr.elab e1 P D G
    let bdy ← SExpr.elab e2 P D ("_" :: s :: G)
    return tmX.app (tm.mkD (tmX.fixlam s bdy)) arg

end

-- test parser for terms
elab "term_parse" "(" p:owl_tm ")" : term =>
    elabTm p

-- check that terms works
elab "Owl_Parse" "{" p:owl_tm "}" : term => do
    elabTm p

@[simp]
def SPhiEntry.elab (S : SPhiEntry) (P : TCtx) : Except String (String × (cond_sym × label P.length)) :=
  match S with
  | .PhiEntry varName condSym lab => do
    let lab' <- lab.elab P
    let cond' <- condSym.elab
    return (varName, (cond', lab'))

@[simp]
def SDeltaEntry.elab (S : SDeltaEntry) (P : TCtx) (D : TCtx) : Except String (String × ty P.length D.length) :=
  match S with
  | .DeltaEntry varName t => do
    let t' <- t.elab P D
    return (varName, t')

@[simp]
def SGammaEntry.elab (S : SGammaEntry) (P : TCtx) (D : TCtx) : Except String (String × ty P.length D.length) :=
  match S with
  | .GammaEntry varName t => do
    let t' <- t.elab P D
    return (varName, t')


@[simp]
def SPsiEntry.elab (S : SPsiEntry) (P : TCtx) : Except String (corruption P.length) :=
  match S with
  | .PsiCorr l1 => do
    let l1' <- l1.elab P
    return .corr l1'
  | .PsiNotCorr l1 => do
    let l1' <- l1.elab P
    return .not_corr l1'

@[simp]
def SPsi.elab (psi : SPsi) (lvars : List String) : Except String (psi_context lvars.length) :=
  match psi with
  | .Psi_End => return (empty_psi lvars.length)
  | .Psi_Cons entry rest => do
    let psi' <- rest.elab lvars
    let corr' <- entry.elab lvars
    return corr' :: psi'

@[simp]
def SPhi.elab (phi : SPhi) : Except String ((vars : List String) × phi_context vars.length) :=
  match phi with
  | .Phi_End => return ⟨[], empty_phi⟩
  | .Phi_Cons entry rest => do
    let ⟨ varNames, phi' ⟩  <- rest.elab
    let (varName, (cond', lab')) <- entry.elab varNames
    return ⟨varName :: varNames, pcons (cond', lab') phi'⟩


@[simp]
def SPhi.getVars (phi : SPhi) : (List String) :=
  match phi with
  | .Phi_End => []
  | .Phi_Cons ⟨varName, _, _⟩ rest => varName :: SPhi.getVars rest

@[simp]
def SDelta.elab (delta : SDelta) (lvars : List String) : Except String ((tvars : List String) × delta_context lvars.length tvars.length) :=
  match delta with
  | .Delta_End => return ⟨[], empty_delta⟩
  | .Delta_Cons entry rest => do
    let ⟨varst, delta'⟩ <- rest.elab lvars
    let ⟨varName, t'⟩ <- entry.elab lvars varst
    return ⟨varName :: varst, dcons t' delta'⟩

@[simp]
def SDelta.getVars (delta : SDelta) : (List String) :=
  match delta with
  | .Delta_End => []
  | .Delta_Cons ⟨varName, _⟩ rest => varName :: SDelta.getVars rest

@[simp]
def SGamma.elab (gamma : SGamma) (lvars : List String) (tvars : List String) : Except String ((vars : List String) × gamma_context lvars.length tvars.length vars.length) :=
  match gamma with
  | .Gamma_End => return ⟨[], empty_gamma⟩
  | .Gamma_Cons t rest => do
    let ⟨vars, gamma'⟩ <- rest.elab lvars tvars
    let ⟨varName, t'⟩ <- t.elab lvars tvars
    return ⟨varName :: vars, cons t' gamma'⟩

@[simp]
def SGamma.getVars (gamma : SGamma) : (List String) :=
  match gamma with
  | .Gamma_End => []
  | .Gamma_Cons ⟨varName, _⟩ rest => varName :: SGamma.getVars rest

@[simp]
def elabHelperTy (s : STy) (lvars : List String) (tvars : List String) : ty lvars.length tvars.length :=
  match STy.elab s lvars tvars with
  | .ok e => e
  | _ => ty.Any --default value

@[simp]
def elabHelperLabel (s : SLabel) (lvars : List String) : label lvars.length :=
  match SLabel.elab s lvars with
  | .ok e => e
  | _ => label.default --default value


@[simp]
def elabHelperConstr (s : SConstr) (lvars : List String) : constr lvars.length :=
  match SConstr.elab s lvars with
  | .ok e => e
  | _ => (.condition .leq .default .default)

@[simp]
def elabHelper (s : SExpr) (lvars : List String) (tvars : List String) (vars : List String) : tm lvars.length tvars.length vars.length :=
  match SExpr.elab s lvars tvars vars with
  | .ok e => e
  | _ => tm.mkD tmX.skip

open Lean Elab Meta

@[simp]
def emptyPhiOfLength : (n : Nat) -> phi_context n
  | 0 => empty_phi
  | n+1 => pcons (.geq, .default) (emptyPhiOfLength n)

@[simp]
def phiWithLength (n : Nat) (sphi : SPhi) : phi_context n :=
  match SPhi.elab sphi with
  | .ok ⟨vars, phi⟩ =>
    if h : vars.length = n then (h ▸ phi) else emptyPhiOfLength n
  | _ => emptyPhiOfLength n

@[simp]
def emptyDeltaOfLength : (l : Nat) -> (t : Nat) -> delta_context l t
  | 0, 0 => empty_delta
  | n+1, t => lift_delta_l (emptyDeltaOfLength n t)
  | n, k+1 => dcons .default (emptyDeltaOfLength n k)

@[simp]
def deltaWithLength (l : Nat) (t : Nat) (sdelta : SDelta) (lvars : List String) : delta_context l t :=
  match SDelta.elab sdelta lvars with
  | .ok ⟨tvars, delta⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        (h2 ▸ (h1 ▸ delta))
      else emptyDeltaOfLength l t
    else emptyDeltaOfLength l t
  | _ => emptyDeltaOfLength l t

@[simp]
def emptyGammaOfLength : (l : Nat) -> (t : Nat) -> (m : Nat) -> gamma_context l t m
  | 0, 0, 0 => empty_gamma
  | n+1, t, m => lift_gamma_l (emptyGammaOfLength n t m)
  | l, k+1, m => lift_gamma_d (emptyGammaOfLength l k m)
  | l, t, j+1 => cons .default (emptyGammaOfLength l t j)

@[simp]
def gammaWithLength (l : Nat) (t : Nat) (m : Nat) (sgamma : SGamma) (lvars : List String) (tvars : List String) : gamma_context l t m :=
  match SGamma.elab sgamma lvars tvars with
  | .ok ⟨vars, gamma⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        if h3 : vars.length = m then
          (h3 ▸ (h2 ▸ (h1 ▸ gamma)))
        else emptyGammaOfLength l t m
      else emptyGammaOfLength l t m
    else emptyGammaOfLength l t m
  | _ => emptyGammaOfLength l t m

@[simp]
def emptyPsiOfLength : (n : Nat) → psi_context n
  | _ => []

@[simp]
def psiWithLength (l : Nat) (spsi : SPsi) (lvars : List String) : psi_context l :=
  match SPsi.elab spsi lvars with
  | .ok psi =>
    if h : lvars.length = l then
      h ▸ psi
    else
      emptyPsiOfLength l
  | _ => emptyPsiOfLength l

-- easier parsing/definitions for phi contexts
@[simp]
elab "Ψ:=" p:owl_phi : term => do
  let sexprPhi ← elabPhi p
  let sVal : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sexprPhi
  match SPhi.elab sVal with
  | .error s   => throwError s!"owl phi: ill-formed term: {s}"
  | .ok ⟨vars, _⟩ =>
    let lenExpr := mkNatLit vars.length
    mkAppM ``phiWithLength #[lenExpr, sexprPhi]


@[simp]
def PhiEntails (phi : phi_context n) (cond : constr n) : Prop :=
  phi |= cond

-- define/parse the relation of Phi |= c
elab "(" phi:owl_phi " ⊨ " cond:owl_constr ")" : term => do

    let sexprPhi ← elabPhi phi

    let sexprConstr <- elabConstr cond

    let sVal : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sexprPhi
    let sVal2 : SConstr ← unsafe do Meta.evalExpr SConstr (mkConst ``SConstr) sexprConstr
    match SPhi.elab sVal, SConstr.elab sVal2 with
    | .ok ⟨vars, _⟩, _ =>
      let lenExpr := mkNatLit vars.length
      let varsExpr ← mkListLit (mkConst ``String) (← vars.mapM (fun s => return mkStrLit s))
      let condE <- mkAppM ``elabHelperConstr #[sexprConstr, varsExpr]
      let phiE <- mkAppM ``phiWithLength #[lenExpr, sexprPhi]
      mkAppM ``PhiEntails #[phiE, condE]
    | .error s, _ => throwError "owl phi: ill-formed term: {s}"

#reduce ((x, y ⊒ x, z ⊒ y, a ⊒ z) ⊨ (x ⊒ fy))

-- define/parse terms easier
@[simp]
elab "Owl" "[" lvars:ident,* "]" "[" tvars:ident,* "]" "[" vars:ident,* "]" "{" p:owl_tm "}" : term => do
  let varNames := vars.getElems.map (fun id => id.getId.toString)
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let varList := varNames.toList
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList

  let varEList ← varNames.mapM (fun s => return mkStrLit s)
  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let tvarEList ← tvarNames.mapM (fun s => return mkStrLit s)

  let varEListExpr ← mkListLit (mkConst ``String) varEList.toList
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList
  let tvarEListExpr ← mkListLit (mkConst ``String) tvarEList.toList

  let sexprTerm ← elabTm p
  let sVal : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm
  match SExpr.elab sVal lvarList tvarList varList with
  | .error s   => throwError "owl: ill-formed term: {s}"
  | .ok _ => mkAppM ``elabHelper #[sexprTerm, lvarEListExpr, tvarEListExpr, varEListExpr]

-- define/parse types easier
@[simp]
elab "OwlTy" "[" lvars:ident,* "]" "[" tvars:ident,* "]" "{" p:owl_type "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList

  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let tvarEList ← tvarNames.mapM (fun s => return mkStrLit s)
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList
  let tvarEListExpr ← mkListLit (mkConst ``String) tvarEList.toList

  let sexprTerm ← elabType p
  let sexprTerm2 ← elabType p

  let sVal : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) sexprTerm2
  match STy.elab sVal lvarList tvarList with
  | .error s  => throwError "owl: ill-formed type: {s}"
  | .ok _ => mkAppM ``elabHelperTy #[sexprTerm, lvarEListExpr, tvarEListExpr]

@[simp]
elab "OwlLabel" "[" lvars:ident,* "]" "{" p:owl_label "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let lvarList := lvarNames.toList

  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList

  let sexprTerm ← elabLabel p

  let sVal : SLabel ← unsafe do Meta.evalExpr SLabel (mkConst ``SLabel) sexprTerm
  match SLabel.elab sVal lvarList with
  | .error s  => throwError "owl: ill-formed label: {s}"
  | .ok _ => mkAppM ``elabHelperLabel #[sexprTerm, lvarEListExpr]


structure Sequent where
  l : Nat
  d : Nat
  m : Nat
  Phi : phi_context l
  Psi : psi_context l
  Delta : delta_context l d
  Gamma : gamma_context l d m
  e : tm l d m
  t : ty l d

def Sequent.has_ty (s : Sequent) :=
  has_type s.Phi s.Psi s.Delta s.Gamma s.e s.t

def addTypeInfo (stx : Syntax) (s : String) := do
    let n : Name := Name.mkSimple s

    withEnableInfoTree true do withLocalDeclD n (mkSort levelOne) fun dslType => do
      let forgedExpr ← mkFreshExprMVar dslType
      pushInfoLeaf <| .ofTermInfo {
        elaborator := `Sequent
        stx := stx
        lctx := (← getLCtx)
        expectedType? := some dslType
        expr := forgedExpr
        isBinder := false
      }
    PURE

def tcVisit l d (o : Owl.opaqueSyntax) (t : Owl.ty l d) : Command.CommandElabM Unit  := do
  Command.liftTermElabM $ addTypeInfo o.inner (toString t)
  PURE

def tcLog (s : String) : Command.CommandElabM Unit := do
  -- Command.liftTermElabM $ logInfo s
  IO.println s
  PURE

syntax "#tc" term "by" tacticSeq : command

open OwlTc


@[simp]
def interpSideConditions (ls : List SideCondition) : Prop :=
  List.foldr (fun i acc => i.interp ∧ acc) True ls

def mkFreshDefn (n : TSyntax `ident) (e : Expr) : Command.CommandElabM Ident := do
  let name := Name.mkStr2 (n.getId.toString) "sideConditions"
  let id := mkIdent name
  Command.liftTermElabM <| do
    -- add definition: freshDef := e
    Lean.addDecl <| .defnDecl {
      name := name,
      levelParams := [],
      type := ← inferType e,
      value := e,
      hints := .abbrev,
      safety := DefinitionSafety.safe
    }
  pure id

def doTc (n : TSyntax `ident) (s : Sequent) tkp pf := do
    match <- OwlTc.infer s.Phi s.Psi s.Delta s.Gamma s.e s.t (CheckState.init tcVisit tcLog) with
    | .ok (_, p) => do
      let sc := p.side_condition
      let id <- mkFreshDefn n (toExpr sc)
      let lemmaName := Name.mkStr2 (n.getId.toString) "soundness"
      let thmCmd <- withRef tkp `(command|
        theorem $(mkIdent lemmaName) : interpSideConditions $id := by $pf
      )
      Command.elabCommand thmCmd
    | .err e =>
      logInfo s!"err: {e.2}"
      match e.1 with
      | .none => PURE
      | .some v =>
        logErrorAt v.inner e.2

    -- Alternatively, use macros or custom translation if Sequent is not a constructor
    -- let s : Sequent := ... -- adjust as needed depending on the definition of Sequent

-- For easier usage of the has_type inductive

syntax "#tc" ident ":=" owl_phi ";" owl_psi ";" owl_delta ";" owl_gamma "⊢" owl_tm ":" owl_type "by" tacticSeq : command
elab_rules : command
  | `(#tc $n := $p ; $ps; $d; $g ⊢ $e : $t by%$tkp $pf ) => do
    let seq_e <- Command.liftTermElabM $ withEnableInfoTree false do

      let sphiExpr2 ← elabPhi p
      let sphi : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sphiExpr2

      let spsiExpr2 ← elabPsi ps
      let spsi : SPsi ← unsafe do Meta.evalExpr SPsi (mkConst ``SPsi) spsiExpr2

      let sdeltaExpr2 ← elabDelta d
      let sdelta : SDelta ← unsafe do Meta.evalExpr SDelta (mkConst ``SDelta) sdeltaExpr2

      let sgammaExpr2 ← elabGamma g
      let sgamma : SGamma ← unsafe do Meta.evalExpr SGamma (mkConst ``SGamma) sgammaExpr2

      let lvars := SPhi.getVars sphi
      let tvars := SDelta.getVars sdelta
      let vars := SGamma.getVars sgamma

      -- ensure all things are properly typed
      match SPhi.elab sphi with
      | .error _ => throwError "owl: ill-formed phi context: {p}"
      | .ok _ => PURE

      match SPsi.elab spsi lvars with
      | .error _ => throwError "owl: ill-formed phi context {ps}"
      | .ok _ => PURE

      match SDelta.elab sdelta lvars with
      | .error _ => throwError "owl: ill-formed delta context {d}"
      | .ok _ => PURE

      match SGamma.elab sgamma lvars tvars with
      | .error _ => throwError "owl: ill-formed gamma context {g}"
      | .ok _ => PURE

      let stmExpr2 ← elabTm e
      let stm : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) stmExpr2

      let styExpr2 ← elabType t
      let sty : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) styExpr2

      match SExpr.elab stm lvars tvars vars with
      | .error _ => throwError "owl: ill-formed term {e}"
      | .ok _ => PURE

      match STy.elab sty lvars tvars with
      | .error _ => throwError "owl: ill-formed type {t}"
      | .ok _ => PURE

      -- prepare to do full evaluation
      let lvarsExpr ← mkListLit (mkConst ``String) (← lvars.mapM (fun s => return mkStrLit s))
      let tvarsExpr ← mkListLit (mkConst ``String) (← tvars.mapM (fun s => return mkStrLit s))
      let varsExpr ← mkListLit (mkConst ``String) (← vars.mapM (fun s => return mkStrLit s))

      let phiExpr ← mkAppM ``phiWithLength #[mkNatLit lvars.length, ← elabPhi p]
      let psiExpr ← mkAppM ``psiWithLength #[mkNatLit lvars.length, ← elabPsi ps, lvarsExpr]
      let deltaExpr ← mkAppM ``deltaWithLength #[mkNatLit lvars.length, mkNatLit tvars.length,
                                              ← elabDelta d, lvarsExpr]
      let gammaExpr ← mkAppM ``gammaWithLength #[mkNatLit lvars.length, mkNatLit tvars.length,
                                                mkNatLit vars.length, ← elabGamma g,
                                                lvarsExpr, tvarsExpr]
      let tyExpr ← mkAppM ``elabHelperTy #[← elabType t, lvarsExpr, tvarsExpr]
      let tmExpr ← mkAppM ``elabHelper #[← elabTm e, lvarsExpr, tvarsExpr, varsExpr]

      mkAppM ``Sequent.mk #[mkNatLit lvars.length, mkNatLit tvars.length, mkNatLit vars.length, phiExpr, psiExpr, deltaExpr, gammaExpr, tmExpr, tyExpr]
    let seq <- Command.liftTermElabM $ unsafe evalExpr Sequent (mkConst `Sequent) seq_e
    doTc n seq tkp pf
