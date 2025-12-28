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

@[simp]
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
  | @embedlabel len l xs =>
      let rec go : List SLabel → Option (List (label P.length))
        | [] => some []
        | x::xs => do
            let res ← SLabel.elab x P
            let rest ← go xs
            some (res :: rest)
      match go xs with
      | none => none
      | some elab_xs =>
          if h : len = elab_xs.length then
            some (subst_label (list_to_finmap elab_xs) (h ▸ l))
          else none
  | .default => .some label.default

@[simp]
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

@[simp]
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
def STy.elab (s : STy) (P : TCtx) (D : TCtx): Option (Owl.ty P.length D.length) :=
  match s with
  | .var_ty i =>
    match TCtx.lookup D i with
    | .none => .none
    | .some j => .some (ty.var_ty j)
  | .Any => .some ty.Any
  | .Unit => .some ty.Unit
  | .Public => .some ty.Public
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
      match (SLabel.elab c P) with
      | .none => .none
      | .some c' =>
        match (STy.elab t1 P D) with
        | .none => .none
        | .some t1' =>
            match (STy.elab t2 P D) with
            | .none => .none
            | .some t2' => .some (ty.t_if c' t1' t2')
  | @embedty llen tlen t ls ts => do
    let rec go1 : List SLabel → Option (List (label P.length))
        | [] => some []
        | x::xs => do
            let res ← SLabel.elab x P
            let rest ← go1 xs
            some (res :: rest)
    let rec go2 : List STy → Option (List (ty P.length D.length))
        | [] => some []
        | x::xs => do
            let res ← STy.elab x P D
            let rest ← go2 xs
            some (res :: rest)
    match go1 ls, go2 ts with
    | .some elab_ls, .some elab_ts =>
      if h : llen = elab_ls.length then
        if k : tlen = elab_ts.length then
          .some (subst_ty (list_to_finmap elab_ls) (list_to_finmap elab_ts) (k ▸ (h ▸ t)))
        else .none
      else .none
    | _, _ => .none
  | .default => .some ty.default

-- test parser for types
elab "type_parse" "(" p:owl_type ")" : term =>
    elabType p

mutual
  @[simp]
  def SExpr.elab (s : SExpr) (P : TCtx) (D : TCtx) (G : TCtx): Option (Owl.tm P.length D.length G.length) :=
    match s with
    | .mk stx v =>
      match SExprX.elab v P D G with
      | .none => .none
      | .some v2 => .some (.mk stx v2)


@[simp]
def SExprX.elab (s : SExprX) (P : TCtx) (D : TCtx) (G : TCtx): Option (Owl.tmX P.length D.length G.length) :=
  match s with
  | .var_tm i =>
    match TCtx.lookup G i with
    | .none => .none
    | .some j => .some (tmX.var_tm j)
  | .error => .some tmX.error
  | .skip => .some tmX.skip
  | .bitstring b =>
    match (SBinary.elab b) with
    | .none => .none
    | .some b' => .some (tmX.bitstring b')
  | .loc n => .some (tmX.loc n)
  | .fixlam f x e =>
    match (SExpr.elab e P D (f::x::G)) with
    | .none => .none
    | .some e' => .some (tmX.fixlam x e')
  | .tlam t e =>
    match (SExpr.elab e P (t::D) G) with
    | .none => .none
    | .some e' => .some (tmX.tlam e')
  | .l_lam l e =>
    match (SExpr.elab e (l::P) D G) with
    | .none => .none
    | .some e' => .some (tmX.l_lam e')
  | .Op op e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tmX.Op op e1' e2')
  | @SExprX.embedtm llen tlen mlen e ls ts es => do
    let rec go1 : List SLabel → Option (List (label P.length))
        | [] => some []
        | x::xs => do
            let res ← SLabel.elab x P
            let rest ← go1 xs
            some (res :: rest)
    let rec go2 : List STy → Option (List (ty P.length D.length))
        | [] => some []
        | x::xs => do
            let res ← STy.elab x P D
            let rest ← go2 xs
            some (res :: rest)
    let rec go3 : List SExpr → Option (List (tm P.length D.length G.length))
        | [] => some []
        | x::xs => do
            let res ← SExpr.elab x P D G
            let rest ← go3 xs
            some (res :: rest)
    match go1 ls, go2 ts, go3 es with
    | .some elab_ls, .some elab_ts, .some elab_es =>
      if h : llen = elab_ls.length then
        if k : tlen = elab_ts.length then
           if j : mlen = elab_es.length then
            .some (subst_tmX (list_to_finmap elab_ls) (list_to_finmap elab_ts) (list_to_finmap elab_es) (j ▸ (k ▸ (h ▸ e.get))))
           else .none
        else .none
      else .none
    | _, _, _ => .none
  | .zero e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.zero e')
  | .app e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tmX.app e1' e2')
  | .alloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.alloc e')
  | .dealloc e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.dealloc e')
  | .assign e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tmX.assign e1' e2')
  | .tm_pair e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' => .some (tmX.tm_pair e1' e2')
  | .left_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.left_tm e')
  | .right_tm e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.right_tm e')
  | .inl e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.inl e')
  | .inr e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.inr e')
  | .case e x1 e1 x2 e2 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P D (x1::G)) with
      | .none => .none
      | .some e1' =>
        match (SExpr.elab e2 P D (x2::G)) with
        | .none => .none
        | .some e2' => .some (tmX.case e' e1' e2')
  | .tapp e t =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (tmX.tapp e' t')
  | .lapp e l =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SLabel.elab l P) with
      | .none => .none
      | .some l' => .some (tmX.lapp e' l')
  | .pack t e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (tmX.pack t' e')
  | .unpack e a x e1 =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SExpr.elab e1 P (a::D) (x::G)) with
      | .none => .none
      | .some e1' => .some (tmX.unpack e' e1')
  | .if_tm e1 e2 e3 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SExpr.elab e3 P D G) with
        | .none => .none
        | .some e3' => .some (tmX.if_tm e1' e2' e3')
  | .if_c c e1 e2 =>
    match (SExpr.elab e1 P D G) with
    | .none => .none
    | .some e1' =>
      match (SExpr.elab e2 P D G) with
      | .none => .none
      | .some e2' =>
        match (SLabel.elab c P) with
        | .none => .none
        | .some c' => .some (tmX.if_c c' e1' e2')
  | .sync e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' => .some (tmX.sync e')
  | .corr_case lab e =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (SLabel.elab lab P) with
      | .none => .none
      | .some lab' => .some (tmX.corr_case lab' e')
  | .annot e t =>
    match (SExpr.elab e P D G) with
    | .none => .none
    | .some e' =>
      match (STy.elab t P D) with
      | .none => .none
      | .some t' => .some (tmX.annot e' t')
  | .default => .some tmX.default
  | .elet s e1 e2 =>
    match SExpr.elab e1 P D G, SExpr.elab e2 P D ("_" :: s :: G) with
    | .some arg, .some bdy => .some (tmX.app (tm.mkD (tmX.fixlam s bdy)) arg)
    | _, _ => .none
end

-- test parser for terms
elab "term_parse" "(" p:owl_tm ")" : term =>
    elabTm p

-- check that terms works
elab "Owl_Parse" "{" p:owl_tm "}" : term => do
    elabTm p

@[simp]
def SPhiEntry.elab (S : SPhiEntry) (P : TCtx) : Option (String × (cond_sym × label P.length)) :=
  match S with
  | .PhiEntry varName condSym lab =>
    match SLabel.elab lab P with
    | .none => .none
    | .some lab' =>
      match SCondSym.elab condSym with
      | .none => .none
      | .some cond' =>
        .some (varName, (cond', lab'))

@[simp]
def SDeltaEntry.elab (S : SDeltaEntry) (P : TCtx) (D : TCtx) : Option (String × ty P.length D.length) :=
  match S with
  | .DeltaEntry varName t =>
    match STy.elab t P D with
    | .none => .none
    | .some t' =>
      .some (varName, t')

@[simp]
def SGammaEntry.elab (S : SGammaEntry) (P : TCtx) (D : TCtx) : Option (String × ty P.length D.length) :=
  match S with
  | .GammaEntry varName t =>
    match STy.elab t P D with
    | .none => .none
    | .some t' =>
      .some (varName, t')

@[simp]
def SPsiEntry.elab (S : SPsiEntry) (P : TCtx) : Option (corruption P.length) :=
  match S with
  | .PsiCorr l1 =>
    match SLabel.elab l1 P with
    | .none => .none
    | .some l1' =>
      .some (.corr l1')
  | .PsiNotCorr l1 =>
    match SLabel.elab l1 P with
    | .none => .none
    | .some l1' =>
      .some (.not_corr l1')

@[simp]
def SPsi.elab (psi : SPsi) (lvars : List String) : Option (psi_context lvars.length) :=
  match psi with
  | .Psi_End => .some (empty_psi lvars.length)
  | .Psi_Cons entry rest =>
    match SPsi.elab rest lvars with
    | .none => .none
    | .some psi' =>
      match SPsiEntry.elab entry lvars with
      | .none => .none
      | .some corr' =>
        .some (corr' :: psi')

@[simp]
def SPhi.elab (phi : SPhi) : Option ((vars : List String) × phi_context vars.length) :=
  match phi with
  | .Phi_End => .some ⟨[], empty_phi⟩
  | .Phi_Cons entry rest =>
    match SPhi.elab rest with
    | .none => .none
    | .some ⟨varNames, phi'⟩ =>
      match SPhiEntry.elab entry varNames with
      | .none => .none
      | .some (varName, (cond', lab')) =>
        .some ⟨varName :: varNames, pcons (cond', lab') phi'⟩

@[simp]
def SPhi.getVars (phi : SPhi) : (List String) :=
  match phi with
  | .Phi_End => []
  | .Phi_Cons ⟨varName, _, _⟩ rest => varName :: SPhi.getVars rest

@[simp]
def SDelta.elab (delta : SDelta) (lvars : List String) : Option ((tvars : List String) × delta_context lvars.length tvars.length) :=
  match delta with
  | .Delta_End => .some ⟨[], empty_delta⟩
  | .Delta_Cons entry rest =>
    match SDelta.elab rest lvars with
    | .none => .none
    | .some ⟨varst, delta'⟩ =>
      match SDeltaEntry.elab entry lvars varst with
      | .none => .none
      | .some ⟨varName, t'⟩ =>
        .some ⟨varName :: varst, dcons t' delta'⟩

@[simp]
def SDelta.getVars (delta : SDelta) : (List String) :=
  match delta with
  | .Delta_End => []
  | .Delta_Cons ⟨varName, _⟩ rest => varName :: SDelta.getVars rest

@[simp]
def SGamma.elab (gamma : SGamma) (lvars : List String) (tvars : List String) : Option ((vars : List String) × gamma_context lvars.length tvars.length vars.length) :=
  match gamma with
  | .Gamma_End => .some ⟨[], empty_gamma⟩
  | .Gamma_Cons t rest =>
    match SGamma.elab rest lvars tvars with
    | .none => .none
    | .some ⟨vars, gamma'⟩ =>
      match SGammaEntry.elab t lvars tvars with
      | .none => .none
      | .some ⟨varName, t'⟩ =>
        .some ⟨varName :: vars, cons t' gamma'⟩

@[simp]
def SGamma.getVars (gamma : SGamma) : (List String) :=
  match gamma with
  | .Gamma_End => []
  | .Gamma_Cons ⟨varName, _⟩ rest => varName :: SGamma.getVars rest

@[simp]
def elabHelperTy (s : STy) (lvars : List String) (tvars : List String) : ty lvars.length tvars.length :=
  match STy.elab s lvars tvars with
  | .some e => e
  | .none => ty.Any --default value

@[simp]
def elabHelperLabel (s : SLabel) (lvars : List String) : label lvars.length :=
  match SLabel.elab s lvars with
  | .some e => e
  | .none => label.default --default value


@[simp]
def elabHelperConstr (s : SConstr) (lvars : List String) : constr lvars.length :=
  match SConstr.elab s lvars with
  | .some e => e
  | .none => (.condition .leq .default .default)

@[simp]
def elabHelper (s : SExpr) (lvars : List String) (tvars : List String) (vars : List String) : tm lvars.length tvars.length vars.length :=
  match SExpr.elab s lvars tvars vars with
  | .some e => e
  | .none => tm.mkD tmX.skip

open Lean Elab Meta

@[simp]
def emptyPhiOfLength : (n : Nat) -> phi_context n
  | 0 => empty_phi
  | n+1 => pcons (.geq, .default) (emptyPhiOfLength n)

@[simp]
def phiWithLength (n : Nat) (sphi : SPhi) : phi_context n :=
  match SPhi.elab sphi with
  | .some ⟨vars, phi⟩ =>
    if h : vars.length = n then (h ▸ phi) else emptyPhiOfLength n
  | .none => emptyPhiOfLength n

@[simp]
def emptyDeltaOfLength : (l : Nat) -> (t : Nat) -> delta_context l t
  | 0, 0 => empty_delta
  | n+1, t => lift_delta_l (emptyDeltaOfLength n t)
  | n, k+1 => dcons .default (emptyDeltaOfLength n k)

@[simp]
def deltaWithLength (l : Nat) (t : Nat) (sdelta : SDelta) (lvars : List String) : delta_context l t :=
  match SDelta.elab sdelta lvars with
  | .some ⟨tvars, delta⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        (h2 ▸ (h1 ▸ delta))
      else emptyDeltaOfLength l t
    else emptyDeltaOfLength l t
  | .none => emptyDeltaOfLength l t

@[simp]
def emptyGammaOfLength : (l : Nat) -> (t : Nat) -> (m : Nat) -> gamma_context l t m
  | 0, 0, 0 => empty_gamma
  | n+1, t, m => lift_gamma_l (emptyGammaOfLength n t m)
  | l, k+1, m => lift_gamma_d (emptyGammaOfLength l k m)
  | l, t, j+1 => cons .default (emptyGammaOfLength l t j)

@[simp]
def gammaWithLength (l : Nat) (t : Nat) (m : Nat) (sgamma : SGamma) (lvars : List String) (tvars : List String) : gamma_context l t m :=
  match SGamma.elab sgamma lvars tvars with
  | .some ⟨vars, gamma⟩ =>
    if h1 : lvars.length = l then
      if h2 : tvars.length = t then
        if h3 : vars.length = m then
          (h3 ▸ (h2 ▸ (h1 ▸ gamma)))
        else emptyGammaOfLength l t m
      else emptyGammaOfLength l t m
    else emptyGammaOfLength l t m
  | .none => emptyGammaOfLength l t m

@[simp]
def emptyPsiOfLength : (n : Nat) → psi_context n
  | _ => []

@[simp]
def psiWithLength (l : Nat) (spsi : SPsi) (lvars : List String) : psi_context l :=
  match SPsi.elab spsi lvars with
  | .some psi =>
    if h : lvars.length = l then
      h ▸ psi
    else
      emptyPsiOfLength l
  | .none => emptyPsiOfLength l

-- easier parsing/definitions for phi contexts
@[simp]
elab "Ψ:=" p:owl_phi : term => do
  let sexprPhi ← elabPhi p
  let sexprPhi2 ← elabPhi_closed p
  let sVal : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sexprPhi2
  match SPhi.elab sVal with
  | .none   => throwError "owl phi: ill-formed term"
  | .some ⟨vars, _⟩ =>
    let lenExpr := mkNatLit vars.length
    mkAppM ``phiWithLength #[lenExpr, sexprPhi]

#reduce Ψ:= ( (x ⊑ ⟨Owl.L.bot⟩) )

@[simp]
def PhiEntails (phi : phi_context n) (cond : constr n) : Prop :=
  phi |= cond

-- define/parse the relation of Phi |= c
elab "(" phi:owl_phi " ⊨ " cond:owl_constr ")" : term => do

    let sexprPhi ← elabPhi phi
    let sexprPhi2 ← elabPhi_closed phi

    let sexprConstr <- elabConstr cond
    let sexprConstr2 <- elabConstr_closed cond

    let sVal : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sexprPhi2
    let sVal2 : SConstr ← unsafe do Meta.evalExpr SConstr (mkConst ``SConstr) sexprConstr2
    match SPhi.elab sVal, SConstr.elab sVal2 with
    | .some ⟨vars, _⟩, _ =>
      let lenExpr := mkNatLit vars.length
      let varsExpr ← mkListLit (mkConst ``String) (← vars.mapM (fun s => return mkStrLit s))
      let condE <- mkAppM ``elabHelperConstr #[sexprConstr, varsExpr]
      let phiE <- mkAppM ``phiWithLength #[lenExpr, sexprPhi]
      mkAppM ``PhiEntails #[phiE, condE]
    | _, _ => throwError "owl phi: ill-formed term"

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
  let sexprTerm2 ← elabTm_closed p
  let sVal : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) sexprTerm2
  match SExpr.elab sVal lvarList tvarList varList with
  | .none   => throwError "owl: ill-formed term"
  | .some _ => mkAppM ``elabHelper #[sexprTerm, lvarEListExpr, tvarEListExpr, varEListExpr]

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
  let sexprTerm2 ← elabType_closed p

  let sVal : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) sexprTerm2
  match STy.elab sVal lvarList tvarList with
  | .none => throwError "owl: ill-formed term"
  | .some _ => mkAppM ``elabHelperTy #[sexprTerm, lvarEListExpr, tvarEListExpr]

@[simp]
elab "OwlLabel" "[" lvars:ident,* "]" "{" p:owl_label "}" : term => do
  let lvarNames := lvars.getElems.map (fun id => id.getId.toString)
  let lvarList := lvarNames.toList

  let lvarEList ← lvarNames.mapM (fun s => return mkStrLit s)
  let lvarEListExpr ← mkListLit (mkConst ``String) lvarEList.toList

  let sexprTerm ← elabLabel p
  let sexprTerm2 ← elabLabel_closed p

  let sVal : SLabel ← unsafe do Meta.evalExpr SLabel (mkConst ``SLabel) sexprTerm2
  match SLabel.elab sVal lvarList with
  | .none => throwError "owl: ill-formed term"
  | .some _ => mkAppM ``elabHelperLabel #[sexprTerm, lvarEListExpr]


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
    pure ()

def tcVisit l d (o : Owl.opaqueSyntax) (t : Owl.ty l d) : Command.CommandElabM Unit  := do
  Command.liftTermElabM $ addTypeInfo o.inner (toString t)
  pure ()

def tcLog (s : String) : Command.CommandElabM Unit := do
  -- Command.liftTermElabM $ logInfo s
  IO.println s
  pure ()

syntax "#tc" term "by" tacticSeq : command

open OwlTc

@[simp]
def interpSideConditions (ls : List SideCondition) : Prop :=
  List.foldr (fun i acc => i.interp ∧ acc) True ls

def mkFreshDefn (e : Expr) : Command.CommandElabM Ident := do
  let lctx ← Command.liftTermElabM $ getLCtx
  let name := LocalContext.getUnusedName lctx `freshDef
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

def doTc (s : Sequent) tkp pf := do
    match <- OwlTc.infer s.Phi s.Psi s.Delta s.Gamma s.e s.t (CheckState.init tcVisit tcLog) with
    | .ok (_, p) => do
      let sc := p.side_condition
      let id <- mkFreshDefn (toExpr sc)
      let lemmaName <- (Command.liftTermElabM $ mkFreshUserName `_)
      let thmCmd <- withRef tkp `(command|
        theorem $(mkIdent lemmaName) : interpSideConditions $id := by $pf
      )
      Command.elabCommand thmCmd
    | .err e =>
      logInfo s!"err: {e.2}"
      match e.1 with
      | .none => pure ()
      | .some v =>
        logErrorAt v.inner e.2

elab_rules : command
  | `(#tc $e by%$tkp $pf:tacticSeq ) => do
    let s ← Command.liftTermElabM $ Lean.Elab.Term.elabTerm e (.some (.const `Sequent []))
    let s <- Command.liftTermElabM $ unsafe evalExpr Sequent (mkConst `Sequent) s
    doTc s tkp pf
    -- Alternatively, use macros or custom translation if Sequent is not a constructor
    -- let s : Sequent := ... -- adjust as needed depending on the definition of Sequent

-- For easier usage of the has_type inductive

syntax "#tc(" owl_phi ";" owl_psi ";" owl_delta ";" owl_gamma "⊢" owl_tm ":" owl_type ")" "by" tacticSeq : command
elab_rules : command
  | `(#tc( $p ; $ps; $d; $g ⊢ $e : $t) by%$tkp $pf ) => do
    let seq_e <- Command.liftTermElabM $ withEnableInfoTree false do

      let sphiExpr2 ← elabPhi_closed p
      let sphi : SPhi ← unsafe do Meta.evalExpr SPhi (mkConst ``SPhi) sphiExpr2

      let spsiExpr2 ← elabPsi_closed ps
      let spsi : SPsi ← unsafe do Meta.evalExpr SPsi (mkConst ``SPsi) spsiExpr2

      let sdeltaExpr2 ← elabDelta_closed d
      let sdelta : SDelta ← unsafe do Meta.evalExpr SDelta (mkConst ``SDelta) sdeltaExpr2

      let sgammaExpr2 ← elabGamma_closed g
      let sgamma : SGamma ← unsafe do Meta.evalExpr SGamma (mkConst ``SGamma) sgammaExpr2

      let lvars := SPhi.getVars sphi
      let tvars := SDelta.getVars sdelta
      let vars := SGamma.getVars sgamma

      -- ensure all things are properly typed
      match SPhi.elab sphi with
      | .none => throwError "owl: ill-formed phi context {p}"
      | .some _ => pure ()

      match SPsi.elab spsi lvars with
      | .none => throwError "owl: ill-formed phi context {ps}"
      | .some _ => pure ()

      match SDelta.elab sdelta lvars with
      | .none => throwError "owl: ill-formed delta context {d}"
      | .some _ => pure ()

      match SGamma.elab sgamma lvars tvars with
      | .none => throwError "owl: ill-formed gamma context {g}"
      | .some _ => pure ()

      let stmExpr2 ← elabTm_closed e
      let stm : SExpr ← unsafe do Meta.evalExpr SExpr (mkConst ``SExpr) stmExpr2

      let styExpr2 ← elabType_closed t
      let sty : STy ← unsafe do Meta.evalExpr STy (mkConst ``STy) styExpr2

      match SExpr.elab stm lvars tvars vars with
      | .none => throwError "owl: ill-formed term {e}"
      | .some _ => pure ()

      match STy.elab sty lvars tvars with
      | .none => throwError "owl: ill-formed type {t}"
      | .some _ => pure ()

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
    doTc seq tkp pf
