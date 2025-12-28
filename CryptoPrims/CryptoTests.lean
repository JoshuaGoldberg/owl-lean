import Lean
import OwlLean.TypeChecker.OwlComplete

open Lean Meta Elab Tactic

open OwlTc

/-
@[simp]
def Sequent.ok (s : Sequent) :=
  OwlTc.has_type_infer s.Phi s.Psi s.Delta s.Gamma s.e s.t
-/


elab "whnf" : tactic => do
  -- 1. Get the current main goal
  let goal ← getMainGoal

  -- 2. Use goal.withContext to ensure we can see local variables
  goal.withContext do
    let reduced ← whnf (<- goal.getType)
    let newGoal ← goal.change reduced
    replaceMainGoal [newGoal]

elab "done" : tactic => do
  -- 1. Get the current main goal
  let goal ← getMainGoal
  match <- goal.getType with
  | .app (.app (.const `OwlTc.TypeError _) stx) e => do
    let s <- unsafe evalExpr String (mkConst ``String) e
    let stx' <- unsafe evalExpr (Option Owl.opaqueSyntax)
      (mkApp (mkConst ``Option [.zero]) (mkConst ``Owl.opaqueSyntax []))
      stx
    let newGoal := Expr.app (.app (.const `OwlTc.TypeError []) stx) (mkStrLit s)
    let newGoal <- goal.change newGoal
    replaceMainGoal [newGoal]
    match stx' with
    | some v =>
      logInfo "got syntax"
      logErrorAt v.inner s
    | _ => pure ()
    logInfo s
  | _ => pure ()



attribute [simp] Fin.foldr_succ

def encI :=
( · ; · ; · ; · ⊢
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    let L = alloc (λ (null : Public) : (tau + unit) => ı2 *) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau)) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), ["0"]) in
                    let L_old = (! L) in
                    let sc = (L := (λ (y : Public) : (tau + unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else (L_old [y]))) in
                    c))
    in
    let dec' : corr (betaK) ? (Public * Public) -> Public : (Data betaK * Public) -> (tau + unit) = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + unit) => (!L) [π2 x]))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), dec'⟩⟩)
    :
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + unit))))))





#check Command.CommandElabM


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

elab_rules : command
  | `(#tc $e by%$tkp $pf:tacticSeq ) => do
    let s ← Command.liftTermElabM $ Lean.Elab.Term.elabTerm e (.some (.const `Sequent []))
    let s <- Command.liftTermElabM $ unsafe evalExpr Sequent (mkConst `Sequent) s
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
    -- Alternatively, use macros or custom translation if Sequent is not a constructor
    -- let s : Sequent := ... -- adjust as needed depending on the definition of Sequent


#tc encI by {
    unfold freshDef
    simp
    grind
}


syntax "#tst" "by" tacticSeq : command

elab_rules : command
  | `(#tst by%$tkp $pf:tacticSeq) => do

    let lemmaName <- (Command.liftTermElabM $ mkFreshUserName `_)

    let thmCmd <- withRef tkp `(command|
      theorem $(mkIdent lemmaName) : True := by $pf
    )
    Command.elabCommand thmCmd

#tst by {
    sorry
}

#check










/-

-- "[0]" represents garbage values not needed for computation
theorem enc_i :
  ( · ; · ; · ; · ⊢
    Λβ betaK .
    Λβ betaM .
    Λ tau .
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    let L = alloc (λ (null : Public) : (tau + Unit) => ı2 *) in
    let enc' = (corr_case betaK in
                (if corr ( betaK )
                  then (λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x))
                  else
                    λ (x : (Data betaK * tau)) : Public =>
                    let c = ⟨"rand"⟩ (zero ((π2 x) : Data betaM), ["0"]) in
                    let L_old = (! L) in
                    let sc = L := (λ (y : Public) : (tau + Unit) => if ⟨"eq"⟩(y, c) then ı1 (π2 x) else L_old [y]) in
                    c))
    in
    let dec' = (corr_case betaK in
               (if corr (betaK) then λ (x : (Public * Public)) : Public => ⟨"dec"⟩(π1 x, π2 x)
                else λ (x : (Data betaK * Public)) : (tau + Unit) => (!L) [π2 x]))
    in
    pack (Data betaK, ⟨k, ⟨(corr_case betaK in enc'), (corr_case betaK in dec')⟩⟩)
    :
    ∀ betaK ⊒ ⟨Owl.L.bot⟩ .
    ∀ betaM ⊏ betaK .
    ∀ tau <: Data betaM .
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))).ok :=
    by
      simp
      whnf
      simp
      done

















      -- Public -> (x + Unit)
      -- x + Unit












/-

open EStateM

theorem enc_ty2 :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ⊢
      pack (Unit, *)
      :
      (∃ alphaK <: Unit . alphaK)) :=
    by
      apply OwlTc.infer_sound
      dsimp [OwlTc.infer, OwlTc.check_subtype, OwlTc.has_type_infer]
      simp [EStateM.run]
      simp [pure, EStateM.pure]





theorem test_let_2 :
  ( · ; · ; · ; · ⊢
      let (x, y) = ⟨* , ["0"]⟩ in
      y
      :
      Public) :=
    by
      apply infer_sound
      simp
      dsimp [infer]
      dsimp [check_subtype]
      simp

theorem test_let_3 :
  ( · ; · ; · ; · ⊢
      let (x, y, z) = ⟨⟨* , *⟩ , ⟨*, ["0"]⟩⟩ in
      z
      :
      Public) :=
    by
    tc_man (
      try simp
      try auto_solve
    )

theorem enc_ty_contra :
  ((betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      (if corr (betaK) then ((λ x => *) : Public -> Unit) else ((λ x => x) : Data betaC -> Data betaC))
      :
      (Public -> Unit)) :=
    by
    tc_man (
      try simp
      auto_solve
    )

theorem enc_length_test :
  ( (betaK, betaM ⊑ betaK, betaC ⊒ betaK) ; (corr(betaK)) ; · ; · ⊢
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ a => λ x => λ x => λ b =>
      λ x => λ x => λ y => λ x => λ h => λ x => λ a => λ x => λ x => λ x => λ x => λ x => λ x => λ x =>
      λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ x => λ z => λ x => λ x => λ x => λ x => λ x => ⟨a, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨x, ⟨z, x⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      :
      (Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->
       Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM -> Data betaM ->

       ((Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * (Public * Public))))))))))))) :=
    by
    tc_man (
      try simp
      auto_solve
    )


theorem enc_r :
  ( (betaK, betaM) ; (corr(betaK)) ; (tau <: Data betaM) ; · ⊢
    let k = (⟨"genKey"⟩ (["0"], ["0"]) : Data betaK) in
    pack (Data betaK, ⟨k, ⟨λ (x : (Public * Public)) : Public => ⟨"enc"⟩ (π1 x, π2 x),
                           λ (y : (Public * Public)) : Public => ⟨"dec"⟩ (π1 y, π2 y)⟩⟩)
    :
    (∃ alphaK <: (Data betaK) . (alphaK *
                                 ((corr (betaK) ? (Public * Public) -> Public : (alphaK * (Data betaM)) -> Public) *
                                  (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit)))))) :=
    by
      simp
      apply infer_sound
      dsimp [infer]
      dsimp [check_subtype]


theorem enc_unpack :
  ( (betaK, betaM ⊑ betaK) ; · ; (tau <: Data betaM) ;
  (E => (∃ alphaK <: (Data betaK) . (alphaK *
                                     ((corr (betaK) ? (Public * Public) -> Public : (alphaK * tau) -> Public) *
                                      (corr (betaK) ? (Public * Public) -> Public : (alphaK * Public) -> (tau + Unit))))),
   x => tau) ⊢
    (corr_case betaK in
     unpack E as (alpha, ked) in
     (π1 (π2 ked)) [⟨(π1 ked), x⟩])
    :
    Public) :=
    by
    tc_man (
      try simp
      auto_solve
    )

-/

abbrev mySeq := ( (l1, l2 ⊒ l1, l3 ⊒ l2) ; · ; (a <: Data l2, b <: Data l1) ;
  (E1 => (∃ alphaK <: (Data l3) .
                        (alphaK *
                         ((corr (l3) ? (Public * Public) -> Public : (alphaK * (Data l2)) -> Public) *
                          (corr (l3) ? (Public * Public) -> Public : (alphaK * Public) -> (a + Unit))))),
   E2 => (∃ alphaK <: (Data l2) .
                        (alphaK *
                         ((corr (l2) ? (Public * Public) -> Public : (alphaK * (Data l1)) -> Public) *
                          (corr (l2) ? (Public * Public) -> Public : (alphaK * Public) -> (b + Unit)))))) ⊢
    (corr_case l3 in
       unpack E1 as (alpha1, ked1) in
       unpack E2 as (alpha2, ked2) in
       (π1 (π2 ked1)) [⟨(π1 ked1), (π1 ked2)⟩])
    :
    Public)




theorem enc_layered :
  mySeq.ok :=  by
    whnf
    simp
    grind

-/
