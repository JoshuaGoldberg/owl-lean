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
    | .some j => return (label.var_label i j)
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


def SRexp.elab (sr : SRexp) (rctx : TCtx) (G : TCtx) : Except String (Owl.rexp rctx.length G.length) :=
  match sr with
  | .var i =>
    match rctx.lookup i with
    | .none => throw s!"Unknown refinement variable: {i} when parsing: {repr sr}"
    | .some j => return (.var j)
  | .op s r1 r2 => do
    let e1 <- r1.elab rctx G
    let e2 <- r2.elab rctx G
    return .op s e1 e2
  | .const i => do
    return .const i
  | .tmvar i =>
    match G.lookup i with
    | .none => throw s!"Unknown term variable: {i} inside of a refinement expression"
    | .some j => return .tmvar j

def SProp.elab (p : SProp) (rctx : TCtx) (G : TCtx) : Except String (Owl.prop rctx.length G.length) :=
  match p with
  | .peq r1 r2 => do
    return .peq (<- r1.elab rctx G) (<- r2.elab rctx G)
  | .pand p1 p2 => do
    return .pand (<- p1.elab rctx G) (<- p2.elab rctx G)
  | .por p1 p2 => do
    return .por (<- p1.elab rctx G) (<- p2.elab rctx G)
  | .pimpl p1 p2 => do
    return .pimpl (<- p1.elab rctx G) (<- p2.elab rctx G)
  | .pnot p1 => do
    return .pnot (<- p1.elab rctx G)
  | .pall s p1 => do
    return .pall (<- p1.elab (s :: rctx) G)

def Fin.from_zero (i : Fin 0) : α := nomatch i

def Owl.ty.lift_g (t : ty l r d 0) : ty l r d g :=
  ren_ty id id id (fun i => Fin.from_zero i) t

@[simp]
def STy.elab (s : STy)
  -- label context
  (P : TCtx)
  -- refinement context
  (R : TCtx)
  -- variable context
  (D : TCtx)
  (G : TCtx)
  : Except String (Owl.ty P.length R.length D.length G.length) :=
  match s with
  | .var_ty i =>
    match TCtx.lookup D i with
    | .none => throw s!"Unknown variable: {i}"
    | .some j => return (ty.var_ty j)
  | .Any => return ty.Any
  | .Unit => return ty.Unit
  | .Public => return ty.Public
  | .RData l re => do
    let l' ← SLabel.elab l P
    let r <- re.elab R G
    return ty.RData l' r
  | .Data l => do
    let l' ← SLabel.elab l P
    return ty.Data l'
  | .Ref t => do
    let t' ← STy.elab t P R D G
    return ty.Ref t'
  | .arr t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.arr t1' t2'
  | .prod t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.prod t1' t2'
  | .sum t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.sum t1' t2'
  | .union t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.union t1' t2'
  | .inter t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.inter t1' t2'
  | .all a t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R (a :: D) G
    return ty.all t1' t2'
  | .refined s p => do
    return .refined (<- STy.elab s P R D G) (<- SProp.elab p R G)
  | .ex a t1 t2 => do
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R (a :: D) G
    return ty.ex t1' t2'
  | .ex_r a t1 => do
    let t1' <- t1.elab P (a :: R) D G
    return .ex_r t1'
  | .all_r a t1 => do
    let t1' <- t1.elab P (a :: R) D G
    return .all_r t1'
  | .all_l s c l t => do
    let c' ← SCondSym.elab c
    let l' ← SLabel.elab l P
    let t' ← STy.elab t (s :: P) R D G
    return ty.all_l c' l' t'
  | .t_if c t1 t2 => do
    let c' ← SLabel.elab c P
    let t1' ← STy.elab t1 P R D G
    let t2' ← STy.elab t2 P R D G
    return ty.t_if c' t1' t2'
  | @embedty llen rlen tlen t ls ts => do
    let elab_ls <- ls.mapM (fun x => SLabel.elab x P)
    let elab_ts <- ts.mapM (fun x => STy.elab x P R D G)
    if h : llen = elab_ls.length then
      if k : tlen = elab_ts.length then
        if h2 : rlen = R.length then
            return subst_ty (list_to_finmap elab_ls) .var (list_to_finmap elab_ts) (k ▸ (h ▸ (h2 ▸ t.lift_g)))
        else
          throw s!"embedty: refinement argument length mismatch"
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
  def SExpr.elab (s : SExpr) (P : TCtx) (R : TCtx) (D : TCtx) (G : TCtx): Except String (Owl.tm P.length R.length D.length G.length) :=
    match s with
    | .mk stx v => do
      let v2 <- SExprX.elab v P R D G
      return (.mk stx v2)

@[simp]
def SExprX.elab (s : SExprX) (P : TCtx) (R:TCtx) (D : TCtx) (G : TCtx): Except String (Owl.tmX P.length R.length D.length G.length) :=
  match s with
  | .var_tm i =>
    match TCtx.lookup G i with
    | .none    => throw s!"SExprX.elab: var index {i} not found in context"
    | .some j  => return tmX.var_tm j
  | .admit => return tmX.admit
  | .error => return tmX.error
  | .skip  => return tmX.skip
  | .bitstring b =>
    return tmX.bitstring b
  | .loc n => return tmX.loc n
  | .fixlam f x e => do
    let e' ← SExpr.elab e P R D (f::x::G)
    return tmX.fixlam x e'
  | .tlam t e => do
    let e' ← SExpr.elab e P R (t::D) G
    return tmX.tlam e'
  | .rlam t e => do
    let e' ← SExpr.elab e P (t :: R) D G
    return tmX.rlam e'
  | .l_lam l e => do
    let e' ← SExpr.elab e (l::P) R D G
    return tmX.l_lam e'
  | .Op op e1 e2 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    return tmX.Op op e1' e2'
  -- | @SExprX.embedtm llen tlen mlen e ls ts es => .error "unimp"
  | .zero e => do
    let e' ← SExpr.elab e P R D G
    return tmX.zero e'
  | .app e1 e2 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    return tmX.app e1' e2'
  | .alloc e => do
    let e' ← SExpr.elab e P R D G
    return tmX.alloc e'
  | .dealloc e => do
    let e' ← SExpr.elab e P R D G
    return tmX.dealloc e'
  | .assign e1 e2 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    return tmX.assign e1' e2'
  | .tm_pair e1 e2 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    return tmX.tm_pair e1' e2'
  | .left_tm e => do
    let e' ← SExpr.elab e P R D G
    return tmX.left_tm e'
  | .right_tm e => do
    let e' ← SExpr.elab e P R D G
    return tmX.right_tm e'
  | .inl e => do
    let e' ← SExpr.elab e P R D G
    return tmX.inl e'
  | .inr e => do
    let e' ← SExpr.elab e P R D G
    return tmX.inr e'
  | .case e x1 e1 x2 e2 => do
    let e' ← SExpr.elab e P R D G
    let e1' ← SExpr.elab e1 P R D (x1 :: G)
    let e2' ← SExpr.elab e2 P R D (x2 :: G)
    return tmX.case e' e1' e2'
  | .tapp e t => do
    let e' ← SExpr.elab e P R D G
    let t' ← STy.elab t P R D G
    return tmX.tapp e' t'
  | .rapp e t => do
    let e' ← SExpr.elab e P R D G
    let t' ← SRexp.elab t R G
    return tmX.rapp e' t'
  | .lapp e l => do
    let e' ← SExpr.elab e P R D G
    let l' ← SLabel.elab l P
    return tmX.lapp e' l'
  | .pack t e => do
    let e' ← SExpr.elab e P R D G
    let t' ← STy.elab t P R D G
    return tmX.pack t' e'
  | .rpack re e => do
    let re' <- SRexp.elab re R G
    let e' <- SExpr.elab e P R D G
    return tmX.rpack re' e'
  | .unpack e a x e1 => do
    let e' ← SExpr.elab e P R D G
    let e1' ← SExpr.elab e1 P R (a::D) (x::G)
    return tmX.unpack e' e1'
  | .if_tm e1 e2 e3 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    let e3' ← SExpr.elab e3 P R D G
    return tmX.if_tm e1' e2' e3'
  | .if_c c e1 e2 => do
    let e1' ← SExpr.elab e1 P R D G
    let e2' ← SExpr.elab e2 P R D G
    let c'  ← SLabel.elab c P
    return tmX.if_c c' e1' e2'
  | .sync e => do
    let e' ← SExpr.elab e P R D G
    return tmX.sync e'
  | .corr_case lab e => do
    let e' ← SExpr.elab e P R D G
    let lab' ← SLabel.elab lab P
    return tmX.corr_case lab' e'
  | .annot e t => do
    let e' ← SExpr.elab e P R D G
    let t' ← STy.elab t P R D G
    return tmX.annot e' t'
  | .default => return tmX.default
  | .elet s e1 e2 => do
    let arg ← SExpr.elab e1 P R D G
    let bdy ← SExpr.elab e2 P R D (s :: G)
    return tmX.tlet arg bdy
  | .union_elim s e1 e2 => do
    let arg ← SExpr.elab e1 P R D G
    let bdy ← SExpr.elab e2 P R D (s :: G)
    return tmX.union_elim arg bdy


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
def SDeltaEntry.elab (S : SDeltaEntry) (P : TCtx) (R: TCtx) (D : TCtx) : Except String (String × ty P.length R.length D.length 0) :=
  match S with
  | .DeltaEntry varName t => do
    let t' <- t.elab P R D []
    return (varName, t')

@[simp]
def SGammaEntry.elab (S : SGammaEntry) (P R : TCtx) (D : TCtx) : Except String (String × ty P.length R.length D.length 0) :=
  match S with
  | .GammaEntry varName t => do
    let t' <- t.elab P R D []
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

def STheta.getVars (theta : STheta) : List String :=
  match theta with
  | .End => []
  | .STheta_var th v => v :: th.getVars
  | .STheta_prop th _ => th.getVars

def STheta.elab (theta : STheta) (rvars : List String) : Except String (List (prop rvars.length 0)) :=
 match theta with
 | .End => return []
 | .STheta_var th _ => th.elab rvars
 | .STheta_prop th p => do
    return (<- p.elab rvars []) :: (<- th.elab rvars)

@[simp]
def SDelta.elab (delta : SDelta) (lvars : List String) (rvars : List String) : Except String ((tvars : List String) × delta_context lvars.length rvars.length tvars.length) :=
  match delta with
  | .Delta_End => return ⟨[], empty_delta⟩
  | .Delta_Cons entry rest => do
    let ⟨varst, delta'⟩ <- rest.elab lvars rvars
    let ⟨varName, t'⟩ <- entry.elab lvars rvars varst
    return ⟨varName :: varst, dcons t' delta'⟩

@[simp]
def SDelta.getVars (delta : SDelta) : (List String) :=
  match delta with
  | .Delta_End => []
  | .Delta_Cons ⟨varName, _⟩ rest => varName :: SDelta.getVars rest

@[simp]
def SGamma.elab (gamma : SGamma) (lvars rvars : List String) (tvars : List String) : Except String ((vars : List String) × gamma_context lvars.length rvars.length tvars.length vars.length) :=
  match gamma with
  | .Gamma_End => return ⟨[], empty_gamma⟩
  | .Gamma_Cons t rest => do
    let ⟨vars, gamma'⟩ <- rest.elab lvars rvars tvars
    let ⟨varName, t'⟩ <- t.elab lvars rvars tvars
    return ⟨varName :: vars, cons t' gamma'⟩

@[simp]
def SGamma.getVars (gamma : SGamma) : (List String) :=
  match gamma with
  | .Gamma_End => []
  | .Gamma_Cons ⟨varName, _⟩ rest => varName :: SGamma.getVars rest

@[simp]
def elabHelperTy (s : STy) (lvars rvars : List String) (tvars : List String) : ty lvars.length rvars.length tvars.length 0 :=
  match STy.elab s lvars rvars tvars [] with
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
def elabHelper (s : SExpr) (lvars rvars : List String) (tvars : List String) (vars : List String) : tm lvars.length rvars.length tvars.length vars.length :=
  match SExpr.elab s lvars rvars tvars vars with
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
def emptyDeltaOfLength : (l : Nat) -> (r : Nat) -> (t : Nat) -> delta_context l r t
  | 0, r, 0 => empty_delta
  | n+1, r, t => lift_delta_l (emptyDeltaOfLength n r t)
  | n, r, k+1 => dcons .default (emptyDeltaOfLength n r k)

@[simp]
def deltaWithLength (l r : Nat) (t : Nat) (sdelta : SDelta) (lvars rvars : List String) : delta_context l r t :=
  match SDelta.elab sdelta lvars rvars with
  | .ok ⟨tvars, delta⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        if h3 : rvars.length = r then
          (h2 ▸ (h1 ▸ (h3 ▸ delta)))
      else emptyDeltaOfLength l r t
      else emptyDeltaOfLength l r t
    else emptyDeltaOfLength l r t
  | _ => emptyDeltaOfLength l r t

@[simp]
def emptyGammaOfLength : (l : Nat) -> (r : Nat) -> (t : Nat) -> (m : Nat) -> gamma_context l r t m
  | 0, r, 0, 0 => empty_gamma
  | n+1, r, t, m => lift_gamma_l (emptyGammaOfLength n r t m)
  | l, r, k+1, m => lift_gamma_d (emptyGammaOfLength l r k m)
  | l, r, t, j+1 => cons .default (emptyGammaOfLength l r t j)

@[simp]
def gammaWithLength (l r : Nat) (t : Nat) (m : Nat) (sgamma : SGamma) (lvars rvars : List String) (tvars : List String) : gamma_context l r t m :=
  match SGamma.elab sgamma lvars rvars tvars with
  | .ok ⟨vars, gamma⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        if h3 : vars.length = m then
          if h4 : rvars.length = r then
            (h3 ▸ (h2 ▸ (h1 ▸ (h4 ▸ gamma))))
        else emptyGammaOfLength l r t m
        else emptyGammaOfLength l r t m
      else emptyGammaOfLength l r t m
    else emptyGammaOfLength l r t m
  | _ => emptyGammaOfLength l r t m

def thetaWithLength (r : Nat) (theta : STheta) (rvars : List String) : OwlTc.RCtx r :=
  match theta.elab rvars with
  | .ok res =>
    if h : rvars.length = r then
      (h ▸ res)
    else []
  | _ => []

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
elab "Owl" "[" lvars:ident,* "]" "[" rvars:ident,* "]" "[" tvars:ident,* "]" "[" vars:ident,* "]" "{" p:owl_tm "}" : term => do
  let varNames := vars.getElems.map (fun id => id.getId.toString)
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let rvarNames := rvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let varList := varNames.toList
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList
  let rvarList := rvarNames.toList

  let varEList ← varNames.mapM (fun s => return mkStrLit s)
  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let rvarEList ← rvarNames.mapM (fun s => return mkStrLit s)
  let tvarEList ← tvarNames.mapM (fun s => return mkStrLit s)

  let varEListExpr ← mkListLit (mkConst ``String) varEList.toList
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList
  let rvarEListExpr ← mkListLit (mkConst ``String) rvarEList.toList
  let tvarEListExpr ← mkListLit (mkConst ``String) tvarEList.toList

  let sexprTerm ← elabTm p
  let sVal : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm
  match SExpr.elab sVal lvarList rvarList tvarList varList with
  | .error s   => throwError "owl: ill-formed term: {s}"
  | .ok _ => mkAppM ``elabHelper #[sexprTerm, lvarEListExpr, rvarEListExpr, tvarEListExpr, varEListExpr]

-- define/parse types easier
/--
  OwlTy_with [ls] [rs] [tvs] :
    ls is set of label variables in scope;

    rs is set of refinement variables in scope;

    tvs is set of type variables in scope

-/
@[simp]
elab "OwlTy_with" "[" lvars:ident,* "]" "[" rvars:ident,* "]" "[" tvars:ident,* "]" "{" p:owl_type "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let rvarNames := rvars.getElems.map (fun id => id.getId.toString)
  let tvarNames := tvars.getElems.map (fun id => id.getId.toString)
  let tvarList := tvarNames.toList
  let lvarList := lvarNames.toList
  let rvarList := rvarNames.toList

  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let rvarEList ← rvarNames.mapM (fun s => return mkStrLit s)
  let tvarEList ← tvarNames.mapM (fun s => return mkStrLit s)
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList
  let rvarEListExpr ← mkListLit (mkConst ``String) rvarEList.toList
  let tvarEListExpr ← mkListLit (mkConst ``String) tvarEList.toList

  let sexprTerm ← elabType p
  let sexprTerm2 ← elabType p

  let sVal : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) sexprTerm2
  match STy.elab sVal lvarList rvarList tvarList [] with
  | .error s  => throwError "owl: ill-formed type: {s}"
  | .ok _ => mkAppM ``elabHelperTy #[sexprTerm, lvarEListExpr, rvarEListExpr, tvarEListExpr]

@[simp]
elab "OwlTy" "{" p:owl_type "}" : term => do
  Term.elabTerm (<- `(OwlTy_with [] [] [] { $p } )) .none


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
  r : Nat
  d : Nat
  m : Nat
  Phi : phi_context l
  Psi : psi_context l
  Delta : delta_context l r d
  Theta : OwlTc.RCtx r
  Gamma : gamma_context l r d m
  e : tm l r d m
  t : ty l r d 0


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

def tcVisit l r d n (o : Owl.opaqueSyntax) (t : Owl.ty l r d n) : Command.CommandElabM Unit  := do
  Command.liftTermElabM $ addTypeInfo o.inner (toString t)
  PURE

def tcLog (s : String) : Command.CommandElabM Unit := do
  -- Command.liftTermElabM $ logInfo s
  IO.println s
  PURE

syntax "#tc" term "by" tacticSeq : command

def tcFresh : Command.CommandElabM Lean.Name :=
  Command.liftCoreM $ mkFreshId

open OwlTc

opaque owl_f_interp' : String -> String -> String -> String

def owl_f_interp (s x y : String) : String :=
  match s with
  | "concat" => x ++ y
  | _ => owl_f_interp' s x y

@[simp]
def interpSideConditions (sc : CheckOutput) : Prop :=
  match sc with
  | .true => True
  | .and e1 e2 => interpSideConditions e1 ∧ interpSideConditions e2
  | .or e1 e2 => interpSideConditions e1 ∨ interpSideConditions e2
  | .sc ⟨_, theta, sc⟩ =>
    (forall bv fv, RCtx.interp theta bv fv owl_f_interp -> sc.eval bv fv owl_f_interp)



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
    match <- OwlTc.infer s.Phi s.Psi s.Delta s.Theta s.Gamma s.e s.t (CheckContext.init tcVisit tcLog tcFresh) with
    | .ok (_, sc) => do
      let sc' := sc.simpl
      let id <- mkFreshDefn n (toExpr sc')
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

syntax "#tc_with" ident ":=" owl_phi ";" owl_psi ";" owl_delta ";" owl_theta ";" owl_gamma "⊢" owl_tm ":" owl_type "by" tacticSeq : command
elab_rules : command
  | `(#tc_with $n := $p ; $ps; $d; $th; $g ⊢ $e : $t by%$tkp $pf ) => do
    let seq_e <- Command.liftTermElabM $ withEnableInfoTree false do

      let sphiExpr2 ← elabPhi p
      let sphi : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sphiExpr2

      let spsiExpr2 ← elabPsi ps
      let spsi : SPsi ← unsafe do Meta.evalExpr SPsi (mkConst ``SPsi) spsiExpr2

      let sdeltaExpr2 ← elabDelta d
      let sdelta : SDelta ← unsafe do Meta.evalExpr SDelta (mkConst ``SDelta) sdeltaExpr2

      let sgammaExpr2 ← elabGamma g
      let sgamma : SGamma ← unsafe do Meta.evalExpr SGamma (mkConst ``SGamma) sgammaExpr2

      let sthetaExpr <- elabTheta th
      let stheta : STheta <- unsafe do Meta.evalExpr STheta (mkConst ``STheta) sthetaExpr

      let lvars := SPhi.getVars sphi
      let rvars : List String := stheta.getVars
        --rs.raw.getArgs.toList.map (fun s => s.getId.toString)

      let tvars := SDelta.getVars sdelta
      let vars := SGamma.getVars sgamma

      -- ensure all things are properly typed
      match SPhi.elab sphi with
      | .error _ => throwError "owl: ill-formed phi context: {p}"
      | .ok _ => PURE

      match SPsi.elab spsi lvars with
      | .error _ => throwError "owl: ill-formed phi context {ps}"
      | .ok _ => PURE

      match SDelta.elab sdelta lvars rvars with
      | .error _ => throwError "owl: ill-formed delta context {d}"
      | .ok _ => PURE

      match SGamma.elab sgamma lvars rvars tvars with
      | .error _ => throwError "owl: ill-formed gamma context {g}"
      | .ok _ => PURE

      match STheta.elab stheta rvars with
      | .error _ => throwError "owl: ill-formed theta context"
      | .ok _ => PURE

      let stmExpr2 ← elabTm e
      let stm : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) stmExpr2

      let styExpr2 ← elabType t
      let sty : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) styExpr2

      match SExpr.elab stm lvars rvars tvars vars with
      | .error s => throwError "owl: ill-formed term: {s}"
      | .ok _ => PURE

      match STy.elab sty lvars rvars tvars [] with
      | .error _ => throwError "owl: ill-formed type {t}"
      | .ok _ => PURE

      -- prepare to do full evaluation
      let lvarsExpr ← mkListLit (mkConst ``String) (← lvars.mapM (fun s => return mkStrLit s))
      let rvarsExpr ← mkListLit (mkConst ``String) (← rvars.mapM (fun s => return mkStrLit s))
      let tvarsExpr ← mkListLit (mkConst ``String) (← tvars.mapM (fun s => return mkStrLit s))
      let varsExpr ← mkListLit (mkConst ``String) (← vars.mapM (fun s => return mkStrLit s))

      let phiExpr ← mkAppM ``phiWithLength #[mkNatLit lvars.length, ← elabPhi p]
      let psiExpr ← mkAppM ``psiWithLength #[mkNatLit lvars.length, ← elabPsi ps, lvarsExpr]
      let deltaExpr ← mkAppM ``deltaWithLength #[mkNatLit lvars.length, mkNatLit rvars.length, mkNatLit tvars.length,
                                              ← elabDelta d, lvarsExpr, rvarsExpr]
      let gammaExpr ← mkAppM ``gammaWithLength #[mkNatLit lvars.length, mkNatLit rvars.length, mkNatLit tvars.length,
                                                mkNatLit vars.length, ← elabGamma g,
                                                lvarsExpr, rvarsExpr, tvarsExpr]
      let thetaExpr <- mkAppM ``thetaWithLength #[mkNatLit rvars.length, <- elabTheta th, rvarsExpr]
      let tyExpr ← mkAppM ``elabHelperTy #[← elabType t, lvarsExpr, rvarsExpr, tvarsExpr]
      let tmExpr ← mkAppM ``elabHelper #[← elabTm e, lvarsExpr, rvarsExpr, tvarsExpr, varsExpr]

      mkAppM ``Sequent.mk #[mkNatLit lvars.length, mkNatLit rvars.length, mkNatLit tvars.length, mkNatLit vars.length, phiExpr, psiExpr, deltaExpr, thetaExpr, gammaExpr, tmExpr, tyExpr]
    let seq <- Command.liftTermElabM $ unsafe evalExpr Sequent (mkConst `Sequent) seq_e
    doTc n seq tkp pf

syntax "#tc" ident ":=" "⊢" "{" owl_tm "}" ":" owl_type "by" tacticSeq : command
elab_rules : command
  | `(#tc $n := ⊢ { $e } : $t by%$_ $pf ) => do
    Command.elabCommand (<- `(#tc_with $n := · ; · ; · ; · ; ·  ⊢ $e : $t by $pf))
