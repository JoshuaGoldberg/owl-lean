import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl
open Lean Meta Elab Tactic

namespace OwlTypecheck

theorem derived_if_typing_annot : forall lab e,
  has_type Phi ((.corr lab) :: Psi) Delta Gamma e t1 ->
  has_type Phi ((.not_corr lab) :: Psi) Delta Gamma e t2 ->
  has_type Phi Psi Delta Gamma e (.t_if lab t1 t2) := by
  intro lab e h1 h2
  apply has_type.T_CorrCase2 lab e (.t_if lab t1 t2)
  apply has_type.T_Sub e t1 (.t_if lab t1 t2)
  apply subtype.ST_RIf1 lab t1 t1 t2
  unfold phi_psi_entail_corr
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  apply subtype.ST_Refl
  exact h1
  apply has_type.T_Sub e t2 (.t_if lab t1 t2)
  apply subtype.ST_RIf2 lab t2 t1 t2
  unfold phi_psi_entail_corr
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_not_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  apply subtype.ST_Refl
  exact h2

theorem derived_if_typing : forall lab e1 e2,
  has_type Phi ((.corr lab) :: Psi) Delta Gamma e1 t1 ->
  has_type Phi ((.not_corr lab) :: Psi) Delta Gamma e2 t2 ->
  has_type Phi Psi Delta Gamma (.if_c lab e1 e2)  (.t_if lab t1 t2) := by
  intro lab e1 e2 h1 h2
  apply has_type.T_CorrCase2 lab (.if_c lab e1 e2)  (.t_if lab t1 t2)
  apply has_type.T_Sub (.if_c lab e1 e2) t1 (.t_if lab t1 t2)
  apply subtype.ST_RIf1 lab t1 t1 t2
  unfold phi_psi_entail_corr
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  apply subtype.ST_Refl
  apply has_type.T_IfCorr2 lab t1 e1 e2
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h1
  apply has_type.T_Sub (.if_c lab e1 e2) t2 (.t_if lab t1 t2)
  apply subtype.ST_RIf2 lab t2 t1 t2
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_not_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  apply subtype.ST_Refl
  apply has_type.T_IfCorr1 lab t2 e1 e2
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_not_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h2

theorem derived_if_subtyping : forall lab t1 t2 t',
  subtype Phi ((.corr lab) :: Psi) Delta t1 t' ->
  subtype Phi ((.not_corr lab) :: Psi) Delta t2 t' ->
  subtype Phi Psi Delta (.t_if lab t1 t2) t' :=
  by
  intro lab t1 t2 t' h1 h2
  apply subtype.ST_Corr
  apply subtype.ST_LIf1
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h1
  apply subtype.ST_LIf2
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_not_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h2

theorem derived_if_subtyping_right : forall lab t t1' t2',
  subtype Phi ((.corr lab) :: Psi) Delta t t1' ->
  subtype Phi ((.not_corr lab) :: Psi) Delta t t2' ->
  subtype Phi Psi Delta t (.t_if lab t1' t2') :=
  by
  intro lab t1 t2 t' h1 h2
  apply subtype.ST_Corr
  apply subtype.ST_RIf1
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h1
  apply subtype.ST_RIf2
  intro pm C vpm Csp
  (repeat constructor)
  cases Csp with
  | psi_not_corr psi C' l $Csp:ident Csp' =>
      exact Csp'
  try simp
  exact h2

-- NEEDED TACTICS
-- has_type
-- subtype
-- phi_entails_c

-- search for a subtype???

-- Give Tlam a subtyping

-- CLAIMS
-- 1. SUBTYPING WILL JUST WORK ON ITS OWN BY BEING THE LAST RULE AND INFERRING
-- 2. LABEL CONSTRAINTS CAN BE ASSUMED AS L.BOT, AND SUBTYPES CAN BE ASSUMED TO HAVE UPPER BOUNDS OF "ANY"

-- TODO
-- check/synthesize
-- Annotation (for synthesis) + *maybe* subtyping notation

-- ALL NEW *Infer* function!!!
structure Conditional (p : Prop) where
  side_condition : Prop
  side_condition_sound : side_condition -> p

structure CheckType (Phi : phi_context l) (Delta : delta_context l d)
                     (Gamma : gamma_context l d m) (e : tm l d m) (exp : ty l d) : Type where
  check : has_type Phi Psi Delta Gamma e exp

structure STType (Phi : phi_context l) (Delta : delta_context l d)
                     (t1 : ty l d) (t2 : ty l d) : Type where
  st : subtype Phi Psi Delta t1 t2

notation:100  "grind" ck => (Conditional.side_condition_sound ck (by grind))

@[simp]
def Conditional.of {p : Prop} (h : p) : Conditional p :=
  ⟨True, fun _ => h⟩



-- TODO : Finish up various cases that have not yet been completed (for check_subtype and infer)!

def check_subtype  (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
                           (t1 : ty l d) (t2 : ty l d) : Option (Conditional (subtype Phi Psi Delta t1 t2)) :=
    match fuel with
    | 0 => .none
    | (n + 1) =>
      match t1, t2 with
      | x, .Any => .some ⟨True, fun _ => subtype.ST_Any x⟩
      | .Unit, .Unit => .some ⟨True, fun _ => subtype.ST_Unit⟩
      | .Data l1, .Data l2 => .some ⟨(Phi |= (.condition .leq l1 l2)), fun sc => subtype.ST_Data l1 l2 sc⟩
      | .Data l1, .Public => .some ⟨( phi_psi_entail_corr Phi Psi (.corr l1)), fun sc => subtype.ST_LPublic l1 sc⟩
      | .var_ty x1, .var_ty x2 =>
        .some ⟨(x1 = x2),
              fun h => by subst h; exact (subtype.ST_Refl (.var_ty x1))⟩
      | .Public, .Public =>
        .some ⟨True, fun sc => subtype.ST_Refl .Public⟩
      | .var_ty x, t' =>
          match check_subtype n Phi Psi Delta (Delta x) t' with
          | .some pf =>
            .some ⟨pf.side_condition,
                  fun sc => subtype.ST_Var x t' (grind pf)⟩
          | .none => .none
      | .Public, .Data l1 =>
        .some ⟨True, fun _ => subtype.ST_RPublic l1⟩
      | (.arr t1 t2), (.arr t1' t2') =>
        match check_subtype n Phi Psi Delta t1' t1, check_subtype n Phi Psi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Func t1' t1 t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | (.prod t1 t2), (.prod t1' t2') =>
        match check_subtype n Phi Psi Delta t1 t1', check_subtype n Phi Psi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Prod t1 t1' t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | (.sum t1 t2), (.sum t1' t2') =>
        match check_subtype n Phi Psi Delta t1 t1', check_subtype n Phi Psi Delta t2 t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc => subtype.ST_Sum t1 t1' t2 t2' (grind pf1) (grind pf2)⟩
        | _, _ => .none
      | .Ref u, .Ref v =>
        .some ⟨(u = v),
              fun h => h ▸ subtype.ST_Ref u⟩
      | .all t0 t, .all t0' t' =>
        match check_subtype n Phi Psi Delta t0 t0' with
        | .some sub_param =>
          let extended_delta := lift_delta (cons t0' Delta)
          match check_subtype n Phi Psi extended_delta t t' with
          | .some sub_body =>
            .some ⟨sub_param.side_condition /\ sub_body.side_condition,
              fun sc =>
                subtype.ST_Univ t0 t0' t t'
                  (grind sub_param)
                  (grind sub_body)⟩
          | .none => .none
        | .none => .none
      | .ex t0 t, .ex t0' t' =>
        match check_subtype n Phi Psi Delta t0 t0' with
        | .some sub1 =>
          let extended_delta := lift_delta (cons t0 Delta)
          match check_subtype n Phi Psi extended_delta t t' with
          | .some sub2 =>
            .some ⟨sub1.side_condition /\ sub2.side_condition,
                  fun ⟨h_witness, h_body⟩ =>
                    subtype.ST_Exist t0 t0' t t'
                      (grind sub1)
                      (grind sub2)⟩
          | .none => .none
        | .none => .none
      | .all_l cs lab t, .all_l cs' lab' t' =>
        let extended_phi := lift_phi (cons (cs, lab) Phi)
        let constraint := (.condition cs (.var_label var_zero) (ren_label shift lab'))
        let constraint_holds := extended_phi |= constraint
        let extended_psi := lift_psi Psi
        let extended_delta := lift_delta_l Delta
        match check_subtype n extended_phi extended_psi extended_delta t t' with
        | .some sub_body =>
          .some ⟨(cs = cs') /\ sub_body.side_condition /\ constraint_holds,
                fun h1 =>
                  match h1 with
                  | ⟨rfl, h3, h4⟩ =>
                    subtype.ST_LatUniv cs lab lab' t t'
                      h4
                      (sub_body.side_condition_sound h3)⟩
        | .none => .none
      | .t_if lab t1 t2, t' =>
        match check_subtype n Phi ((.corr lab) :: Psi) Delta t1 t',
              check_subtype n Phi ((.not_corr lab) :: Psi) Delta t2 t' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition ,
            fun sc =>
              derived_if_subtyping lab t1 t2 t'
                (pf1.side_condition_sound sc.left)
                (pf2.side_condition_sound sc.right)⟩
        | _, _ =>
          match check_subtype n Phi Psi Delta t1 t',
                check_subtype n Phi Psi Delta t2 t' with
          | .some pf1, .none =>
            .some ⟨pf1.side_condition /\ phi_psi_entail_corr Phi Psi (.corr lab),
                  fun sc => subtype.ST_LIf1 lab t1 t2 t' sc.right (grind pf1)⟩
          | .none, .some pf2 =>
            .some ⟨pf2.side_condition /\ phi_psi_entail_corr Phi Psi (.not_corr lab),
                  fun sc => subtype.ST_LIf2 lab t1 t2 t' sc.right (grind pf2)⟩
          | _, _ => .none
      | t, .t_if lab t1' t2' =>
        match check_subtype n Phi ((.corr lab) :: Psi) Delta t t1',
              check_subtype n Phi ((.not_corr lab) :: Psi) Delta t t2' with
        | .some pf1, .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                fun sc =>
                  derived_if_subtyping_right lab t t1' t2'
                    (pf1.side_condition_sound sc.left)
                    (pf2.side_condition_sound sc.right)⟩
        | _, _ =>
          match check_subtype n Phi Psi Delta t t1',
                check_subtype n Phi Psi Delta t t2' with
          | .some pf1, .none =>
            .some ⟨pf1.side_condition /\ phi_psi_entail_corr Phi Psi (.corr lab),
                  fun sc => subtype.ST_RIf1 lab t t1' t2' sc.right (grind pf1)⟩
          | .none, .some pf2 =>
            .some ⟨pf2.side_condition /\ phi_psi_entail_corr Phi Psi (.not_corr lab),
                  fun sc => subtype.ST_RIf2 lab t t1' t2' sc.right (grind pf2)⟩
          | .some pf1, .some pf2 =>
            let corr_cond := phi_psi_entail_corr Phi Psi (.corr lab)
            .some ⟨pf1.side_condition /\ corr_cond,
                  fun sc => subtype.ST_RIf1 lab t t1' t2' sc.right (grind pf1)⟩
          | .none, .none => .none
      | x1, x2 =>
        .none

@[simp]
def to_data (fuel : Nat) (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d) (t : ty l d)
  : Option ((l : Owl.label l) × (PLift (subtype Phi Psi Delta t (.Data l)))) :=
    match fuel with
    | 0 => .none
    | n + 1 =>
      match t with
      | .Data l1 => .some ⟨l1, PLift.up (by apply subtype.ST_Refl)⟩
      | .Public => .some ⟨.latl L.bot, PLift.up (by
          constructor
      )⟩
      | .var_ty x =>
        match (to_data n Phi Psi Delta (Delta x)) with
        | .some ⟨lab, pf⟩ =>
          .some ⟨lab, (PLift.up (subtype.ST_Var x (.Data lab) pf.down))⟩
        | .none => .none
      | _ => .none

@[simp]
def unifies (t1 : ty l d) (exp : Option (ty l d)) :=
  PLift (match exp with
          | .none => True
          | .some t2 => t1 = t2
  )

@[simp]
def from_synth (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) {e : tm l d m} (t1 : ty l d) (h : Conditional (has_type Phi Psi Delta Gamma e t1)) (exp : Option (ty l d)) :
          Option ((t : ty l d) × unifies t exp × Conditional (has_type Phi Psi Delta Gamma e t)) :=
    match exp with
    | .none => .some ⟨t1, ⟨by apply PLift.up; simp, h⟩⟩
    | .some t =>
      match check_subtype 999 Phi Psi Delta t1 t with
      | .none => .none
      | .some pf =>
        .some ⟨t, ⟨by apply PLift.up; simp, ⟨ pf.side_condition ∧ h.side_condition, fun sc => by
            apply has_type.T_Sub
            apply (pf.side_condition_sound (by grind))
            apply (h.side_condition_sound (by grind))⟩⟩ ⟩



-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"
-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type
def infer (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          Option ((t : ty l d) × unifies t exp × Conditional (has_type Phi Psi Delta Gamma e t)) :=
  match e with
  | .var_tm x =>
      from_synth Phi Psi Delta Gamma _ (Conditional.of $ (has_type.T_Var x)) exp
  | .skip =>
      from_synth Phi Psi Delta Gamma _ (Conditional.of $ (has_type.T_IUnit)) exp
  | .bitstring b =>
      from_synth Phi Psi Delta Gamma _ (Conditional.of $ (has_type.T_Const b)) exp
  | .Op op e1 e2 => -- This case is long! Might need a step by step.
    match infer Phi Psi Delta Gamma e1 .none, infer Phi Psi Delta Gamma e2 .none with
    | some ⟨t1, pf1⟩, some ⟨t2, pf2⟩ =>
      match to_data 99 Phi Psi Delta t1, to_data 99 Phi Psi Delta t2 with
      | .some ⟨l1, pf11⟩, .some ⟨l2, pf12⟩ =>
        from_synth Phi Psi Delta Gamma _ ⟨pf1.snd.side_condition ∧ pf2.snd.side_condition ∧ (Phi |= (.condition .leq l2 l1)),
              fun sc => by
                apply has_type.T_Op
                apply has_type.T_Sub
                apply pf11.down
                apply pf1.snd.side_condition_sound

                grind
                apply has_type.T_Sub
                apply subtype.ST_Data
                obtain ⟨_, ⟨_, h⟩⟩ := sc
                apply h
                apply has_type.T_Sub
                apply pf12.down
                apply pf2.snd.side_condition_sound
                grind ⟩ exp
      | _, _ => .none
    | _, _ => .none
  | .zero e =>
    match infer Phi Psi Delta Gamma e .none with
    | .none => .none
    | .some ⟨t1, pf⟩ =>
      match to_data 9 Phi Psi Delta t1 with
      | .none => .none
      | .some ⟨l, pf2⟩ =>
          from_synth Phi Psi Delta Gamma _ ⟨pf.snd.side_condition, fun sc => by
              apply has_type.T_Zero
              apply has_type.T_Sub
              apply pf2.down
              apply pf.snd.side_condition_sound
              apply sc⟩ exp
  | .if_tm e e1 e2 =>
    match infer Phi Psi Delta Gamma e (.some .Public) with
    | .none => .none
    | .some ⟨t1, ⟨heq, pf⟩⟩ =>
      match infer Phi Psi Delta Gamma e1 exp, infer Phi Psi Delta Gamma e2 exp with
      | .some ⟨t11, ⟨heq1, pf1⟩⟩, .some ⟨t12, ⟨heq2, pf2⟩⟩ =>
        match check_subtype 99 Phi Psi Delta t12 t11 with
        | .none => .none
        | .some pf3 =>
            from_synth Phi Psi Delta Gamma t11 ⟨pf.side_condition ∧ pf1.side_condition ∧ pf2.side_condition ∧ pf3.side_condition, fun sc =>
              by
                apply has_type.T_If
                simp at heq
                have heq' : t1 = .Public := by apply heq.down
                subst heq'
                apply pf.side_condition_sound
                grind
                apply pf1.side_condition_sound; grind
                apply has_type.T_Sub
                apply pf3.side_condition_sound; grind
                apply pf2.side_condition_sound; grind⟩ exp
      | _, _ => .none
  | .alloc e =>
    match infer Phi Psi Delta Gamma e .none with
    | .none => .none
    | .some ⟨t,⟨heq,pf⟩⟩ =>
      from_synth Phi Psi Delta Gamma (.Ref t) ⟨pf.side_condition, fun sc => by
        apply has_type.T_IRef
        apply pf.side_condition_sound; grind
        ⟩
      exp
  | .dealloc e =>
    match infer Phi Psi Delta Gamma e .none with
    | .none => .none
    | .some ⟨.Ref t,⟨heq,pf⟩⟩ =>
      from_synth Phi Psi Delta Gamma (t) ⟨pf.side_condition, fun sc => by
        apply has_type.T_ERef
        apply pf.side_condition_sound; grind
        ⟩
      exp
    | .some _ => .none
  | .assign e1 e2 =>
    match infer Phi Psi Delta Gamma e1 .none with
    | .some ⟨.Ref t,⟨_, pf⟩⟩ =>
      match infer Phi Psi Delta Gamma e2 (.some t) with
      | .some ⟨t1, ⟨heq, pf'⟩⟩ =>
        from_synth Phi Psi Delta Gamma .Unit ⟨pf.side_condition ∧ pf'.side_condition, fun sc => by
          apply has_type.T_Assign
          apply pf.side_condition_sound
          grind
          have heq' : t1 = t := heq.down
          subst heq'
          apply pf'.side_condition_sound; grind
        ⟩ exp
      | .none => .none
    | _ => .none
  | .inl e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort! (No need to add right now)
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer Phi Psi Delta Gamma e (.some t1) with
        | .some ⟨t1, ⟨heq, pf⟩⟩ => .some ⟨.sum t1 t2, ⟨by
          simp at heq; cases heq; rename_i h; subst h
          apply PLift.up; simp
        , ⟨pf.side_condition, fun sc => by
            apply has_type.T_ISumL
            apply pf.side_condition_sound; grind
          ⟩⟩⟩
        | .none => .none
      | _ => .none
  | .inr e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort! (No need to add right now)
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer Phi Psi Delta Gamma e (.some t2) with
        | .some ⟨t2, ⟨heq, pf⟩⟩ => .some ⟨.sum t1 t2, ⟨by
        simp at heq
        cases heq
        simp
        apply PLift.up
        grind
        , ⟨pf.side_condition, fun sc => by
            apply has_type.T_ISumR
            apply pf.side_condition_sound; grind
          ⟩⟩⟩
        | .none => .none
      | _ => .none
  | .fixlam e =>
    match exp with
    | .none => .none -- TODO, allow synthesis
    | .some t =>
      match t with
      | .arr t t' =>
        let extended_gamma := cons (.arr t t') (cons t Gamma)
        match infer Phi Psi Delta extended_gamma e (.some t') with
        | .some ⟨t1, ⟨heq, pf⟩⟩ => .some
            ⟨.arr t t', ⟨by
              have heq' : t1 = t' := heq.down
              subst heq'
              apply PLift.up
              grind,
            ⟨pf.side_condition, fun sc => by
              apply has_type.T_IFun
              have heq' : t1 = t' := heq.down
              subst heq'
              apply pf.side_condition_sound; grind
          ⟩⟩⟩

        | .none => .none
      | _ => .none
  | .app e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e1 .none with
      | .none => .none
      | .some ⟨.arr t t', ⟨heq, pf⟩⟩ =>
        match infer Phi Psi Delta Gamma e2 (.some t) with
        | .none => .none
        | .some ⟨t1, ⟨heq', pf'⟩⟩ =>
          from_synth Phi Psi Delta Gamma t' ⟨pf.side_condition ∧ pf'.side_condition, fun sc => by
            apply has_type.T_EFun
            apply pf.side_condition_sound; grind
            have : t1 = t := heq'.down
            subst this
            apply pf'.side_condition_sound; grind
          ⟩ .none
      | _ => .none
    | .some expected =>
      match infer Phi Psi Delta Gamma e2 .none with
      | .none => .none
      | .some ⟨t1, ⟨_, pf⟩⟩ =>
        match infer Phi Psi Delta Gamma e1 (.some (.arr t1 expected)) with
        | .none => .none
        | .some ⟨tres, ⟨heq, pf2⟩⟩ =>
          .some ⟨expected, ⟨by apply PLift.up; simp, ⟨pf.side_condition ∧ pf2.side_condition, fun sc => by
              apply has_type.T_EFun
              simp at heq
              cases heq
              rename_i h
              subst h
              apply pf2.side_condition_sound; grind
              apply pf.side_condition_sound; grind
              ⟩⟩⟩
  | .tm_pair e1 e2 =>
    match infer Phi Psi Delta Gamma e1 .none, infer Phi Psi Delta Gamma e2 .none with
    | .some ⟨t1, ⟨heq1, pf1⟩⟩, .some ⟨t2, ⟨heq2, pf2⟩⟩ =>
      from_synth Phi Psi Delta Gamma (.prod t1 t2) ⟨pf1.side_condition ∧ pf2.side_condition, fun sc => by
        apply has_type.T_IProd
        apply pf1.side_condition_sound; grind
        apply pf2.side_condition_sound; grind
      ⟩ exp
    | _, _ => .none
  | .left_tm e =>
    match infer Phi Psi Delta Gamma e .none with
    | .none => .none
    | .some ⟨.prod t1 t2, ⟨heq, pf⟩⟩ =>
      from_synth Phi Psi Delta Gamma t1 ⟨pf.side_condition, fun sc => by
        apply has_type.T_EProdL
        apply pf.side_condition_sound; grind
      ⟩ exp
    | _ => .none
  | .right_tm e =>
    match infer Phi Psi Delta Gamma e .none with
    | .none => .none
    | .some ⟨.prod t1 t2, ⟨heq, pf⟩⟩ =>
      from_synth Phi Psi Delta Gamma t2 ⟨pf.side_condition, fun sc => by
        apply has_type.T_EProdR
        apply pf.side_condition_sound; grind
      ⟩ exp
    | _ => .none
  | .case e e1 e2 =>
    match infer Phi Psi Delta Gamma e .none with
    | .some ⟨.sum t1 t2, ⟨heq, pf⟩⟩ =>
      match infer Phi Psi Delta (cons t1 Gamma) e1 (.some t1), infer Phi Psi Delta (cons t2 Gamma) e2 (.some t2) with
      | .some ⟨r1, ⟨heq1, pf1⟩⟩, .some ⟨r2, ⟨heq2, pf2⟩⟩ =>
        match exp with
        | .some res =>
          match check_subtype 999 Phi Psi Delta r1 res, check_subtype 999 Phi Psi Delta r2 res with
          | .some pf3, .some pf4 =>
            .some ⟨res, ⟨by apply PLift.up; simp, ⟨pf.side_condition ∧ pf1.side_condition ∧ pf2.side_condition ∧ pf3.side_condition ∧ pf4.side_condition
            , fun sc => by
              apply has_type.T_ESum
              apply pf.side_condition_sound; grind
              apply has_type.T_Sub
              apply pf3.side_condition_sound; grind
              apply pf1.side_condition_sound; grind
              apply has_type.T_Sub
              apply pf4.side_condition_sound; grind
              apply pf2.side_condition_sound; grind
        ⟩⟩⟩
          | _, _ => .none
        | .none =>
          match check_subtype 999 Phi Psi Delta r2 r1 with
          | .none => .none
          | .some pf3 =>
            .some ⟨r1, ⟨by apply PLift.up; simp, ⟨pf.side_condition ∧ pf1.side_condition ∧ pf2.side_condition ∧ pf3.side_condition, fun sc => by
              apply has_type.T_ESum
              apply pf.side_condition_sound; grind
              apply pf1.side_condition_sound; grind
              apply has_type.T_Sub
              apply pf3.side_condition_sound; grind
              apply pf2.side_condition_sound; grind
            ⟩⟩⟩
      | _, _ => .none
    | _ => .none
  | .tlam e =>
    match exp with
    | .none => .none  -- TODO : Synthesize!!!
    | .some (.all t0 t) =>
      match infer Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t) with
      | .some ⟨res, ⟨heq, pf⟩⟩ =>
        .some ⟨.all t0 t, ⟨by apply PLift.up; simp, ⟨pf.side_condition,
                   fun sc =>  by
                    have: res = t := heq.down
                    subst this
                    apply has_type.T_IUniv
                    apply pf.side_condition_sound; grind
                    ⟩⟩⟩
      | .none => .none
    | _ => .none
  | .tapp e t' =>
    match infer Phi Psi Delta Gamma e .none with
    | .some ⟨.all t0 t, ⟨heq, pf1⟩⟩ =>
      match check_subtype 99 Phi Psi Delta t' t0 with
      | .none => .none
      | .some pf =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t;
          from_synth Phi Psi Delta Gamma result_ty ⟨pf1.side_condition ∧ pf.side_condition,
            fun sc => by
              apply has_type.T_EUniv
              apply pf.side_condition_sound; grind
              apply pf1.side_condition_sound; grind
              ⟩  exp
    | _ => .none
  | .pack t' e =>
    match exp with
    | .none => .none -- TODO : potentially ADD Synthesis!
    | .some (.ex t0 t) =>
      let substituted_type := subst_ty .var_label (cons t' .var_ty) t
      match check_subtype 99 Phi Psi Delta t' t0 with
      | .some sub =>
        match infer Phi Psi Delta Gamma e (.some substituted_type) with
        | .some ⟨r, ⟨heq, pf⟩⟩ =>
          .some ⟨.ex t0 t, ⟨by
            simp at heq; cases heq; rename_i h; subst h
            apply PLift.up; simp
          , ⟨pf.side_condition /\ sub.side_condition,
                 fun sc => by
                  have h0 := heq.down
                  simp at h0
                  subst h0
                  apply has_type.T_IExist
                  apply pf.side_condition_sound; grind
                  apply sub.side_condition_sound; grind
        ⟩⟩⟩
        | .none => .none
      | .none => .none
    | _ => .none
  | .unpack e e' =>
    match exp with
    | .none => .none  -- TODO
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.ex t0 t, ⟨_, pf_e⟩⟩ =>
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id shift exp_ty
        match infer Phi Psi extended_delta extended_gamma e' (.some renamed_t') with
        | .some ⟨res, ⟨heq, pf_e'⟩⟩ =>
          .some ⟨exp_ty, ⟨by apply PLift.up; simp, ⟨pf_e.side_condition ∧ pf_e'.side_condition,
              fun sc => by
                apply has_type.T_EExist
                apply pf_e.side_condition_sound;grind
                have h0 := heq.down; simp at h0; subst h0
                apply pf_e'.side_condition_sound;grind
              ⟩ ⟩ ⟩
        | .none => .none
      | _ => .none
  | .l_lam e =>
    match exp with
    | .none => .none -- TODO
    | .some exp_ty =>
      match h : exp_ty with
      | .all_l cs lab t_body =>
         match infer (lift_phi ((cons (cs, lab)) Phi))
                  (lift_psi Psi)
                  (lift_delta_l Delta) (lift_gamma_l Gamma)
                  e (.some t_body) with
         | .some ⟨res, ⟨heq, pe⟩⟩  =>
           .some ⟨exp_ty, ⟨by subst h; apply PLift.up; simp, ⟨
           pe.side_condition,
               fun sc => by
                subst h
                apply has_type.T_ILUniv
                have h0 := heq.down; simp at h0; subst h0
                apply pe.side_condition_sound; grind
          ⟩⟩⟩ --
         | .none => .none
      | _ => .none
  | .lapp e lab' =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, ⟨_, pf⟩⟩  =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        let constraint_obligation := (Phi |= (.condition cs lab lab'))
        .some ⟨result_ty, ⟨by apply PLift.up; simp,
              ⟨pf.side_condition /\ constraint_obligation,
                fun sc =>
                  has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf)⟩⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, ⟨_, pf⟩⟩  =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        match check_subtype 99 Phi Psi Delta result_ty exp_ty with
        | .some sub_pf =>
          let constraint_obligation := (Phi |= (.condition cs lab lab'))
          .some ⟨exp_ty, ⟨by apply PLift.up; simp, ⟨pf.side_condition /\ constraint_obligation /\ sub_pf.side_condition,
                fun sc =>
                  has_type.T_Sub (.lapp e lab') result_ty exp_ty
                    (grind sub_pf)
                    (has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf))⟩⟩ ⟩
        | .none => .none
      | _ => .none
  | .annot e t' => -- LONG CASE TO HANDLE IF CHECKING PROPERLY
    match infer Phi Psi Delta Gamma e (.some t') with
    | .none => .none
    | .some ⟨res, ⟨heq, pf⟩⟩ =>
      from_synth Phi Psi Delta Gamma res ⟨pf.side_condition, fun sc => by
        have h0 := heq.down; simp at h0; subst h0
        apply has_type.T_Annot
        apply pf.side_condition_sound; grind
      ⟩ exp
  | .if_c lab e1 e2 =>
      match infer Phi ((.corr lab) :: Psi) Delta Gamma e1 none,
            infer Phi ((.not_corr lab) :: Psi) Delta Gamma e2 none with
      | some ⟨t1, ⟨_, pf1⟩⟩, some ⟨t2, ⟨_, pf2⟩⟩ =>
        from_synth Phi Psi Delta Gamma (.t_if lab t1 t2) ⟨pf1.side_condition ∧  pf2.side_condition, fun sc => by
          apply derived_if_typing
          apply pf1.side_condition_sound; grind
          apply pf2.side_condition_sound; grind
        ⟩ exp
      | _, _ => .none
  | .corr_case lab e =>
    match exp with
    | .none =>
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      match infer Phi psi_corr Delta Gamma e .none, infer Phi psi_not_corr Delta Gamma e .none with
      | .some ⟨t1, ⟨_, pf1⟩⟩, .some ⟨t2, ⟨_, pf2⟩⟩ =>
          match check_subtype 99 Phi psi_not_corr Delta t2 t1 with
          | .some sub12 =>
            .some ⟨t1, ⟨by apply PLift.up; simp, ⟨pf1.side_condition ∧ pf2.side_condition ∧ sub12.side_condition, fun sc => by
              apply has_type.T_CorrCase
              apply pf1.side_condition_sound; grind
              apply has_type.T_Sub
              apply sub12.side_condition_sound; grind
              apply pf2.side_condition_sound; grind
            ⟩⟩⟩
          | .none => none
      | _, _ => .none
    | .some exp_ty =>
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      match infer Phi psi_corr Delta Gamma e (.some exp_ty), infer Phi psi_not_corr Delta Gamma e (.some exp_ty) with
      | .some ⟨r1, ⟨heq1, pf1⟩⟩, .some ⟨r2, ⟨heq2, pf2⟩⟩  =>
        .some ⟨exp_ty, ⟨by apply PLift.up; simp,
        ⟨pf1.side_condition /\ pf2.side_condition,
            fun sc => by
              have h0 := heq1.down; simp at h0; subst h0
              have h1 := heq2.down; simp at h1; subst h1
              apply has_type.T_CorrCase
              apply pf1.side_condition_sound; grind
              apply pf2.side_condition_sound; grind
          ⟩⟩⟩
      | _, _ => .none
  | .sync e =>
      match infer Phi Psi Delta Gamma e (.some .Public) with
      | .some ⟨res, ⟨heq,  pf1⟩⟩ =>
        from_synth Phi Psi Delta Gamma .Public
          ⟨pf1.side_condition, fun sc => by
            have h0 := heq.down; simp at h0; subst h0
            apply has_type.T_Sync e (grind pf1)⟩ exp
      | .none => .none
  | _ =>
    match exp with
    | .some _ => .none
    | .none => .none
  -- TODO CORR cases for infer and check_subtype (adding corruptions to justify types) (may be done)

theorem infer_sound (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (t : ty l d) res heq :
          forall cond,
           infer Phi Psi Delta Gamma e (some t) = some ⟨res, ⟨heq, cond⟩⟩ →
           cond.side_condition →
           has_type Phi Psi Delta Gamma e t := by
  intro cond h1 h2
  have h0 := heq.down; simp at h0; subst h0
  apply cond.side_condition_sound
  apply h2

theorem infer_sound_none (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) :
  (forall result, infer Phi Psi Delta Gamma e none = some result ->
          result.snd.snd.side_condition ->
          has_type Phi Psi Delta Gamma e result.fst) := by
  intros cond h1 h2
  simp at cond
  have cond' := cond.snd.snd.side_condition_sound
  apply cond'
  apply h2

def simple_test_delta :=
   (dcons .Unit (@empty_delta 0))

def test_delta_2 :=
   (dcons (.var_ty ⟨0, by omega⟩) simple_test_delta)

def simple_test_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩) (pcons (.geq, .latl L.bot) empty_phi))

def simple_test_gamma : gamma_context 0 0 1 :=
  (cons .Unit empty_gamma)

theorem cons_surjective {n : Nat} (f : Fin (n + 1) → label 0) :
  ∃ (head : label 0) (tail : Fin n → label 0),
    f = cons head tail := by
  exists f 0
  exists (fun i => f i.succ)
  funext i
  cases i using Fin.cases
  · rfl
  · rfl

theorem ren_label_injective
  (h : forall x y, xi x = xi y -> x = y) :
  forall s1 s2, ren_label xi s1 = ren_label xi s2 → s1 = s2 := by
  intro s1 s2 heq
  induction s1 generalizing s2 with
  | var_label x =>
      cases s2 <;> simp [ren_label] at heq
      congr
      exact h _ _ heq
  | latl l =>
      cases s2 <;> simp [ren_label] at heq
      subst heq
      rfl
  | ljoin l1 l2 ih1 ih2 =>
      cases s2 <;> simp [ren_label] at heq
      congr
      · exact ih1 _ heq.1
      · exact ih2 _ heq.2
  | lmeet l1 l2 ih1 ih2 =>
      cases s2 <;> simp [ren_label] at heq
      congr
      · exact ih1 _ heq.1
      · exact ih2 _ heq.2
  | default =>
      cases s2 <;> simp [ren_label] at heq
      rfl

theorem shift_injective : forall (x : Fin l) (y : Fin l), shift x = shift y -> x = y := by
  intro x y h
  simp [shift] at h
  exact h

syntax "tc_full" term:max term:max term:max term:max term:max term:max tactic : tactic
syntax "tc_full_man" term:max term:max term:max term:max term:max term:max tactic : tactic
syntax "tc" tactic:max : tactic
syntax "tc_man" tactic:max : tactic
syntax "auto_solve_fast" : tactic
syntax "solve_phi_validation" ident : tactic
syntax "attempt_solve" : tactic
syntax "solve_phi_validation_anon" : tactic
syntax "solve_phi_validation_anon_no_simp" : tactic
syntax "case_phi " ident ident ident num num : tactic
syntax "case_phi_corr" ident ident ident ident num num : tactic
syntax "all_ren" ident ident num num : tactic
syntax "check_corr" ident ident ident : tactic
syntax "destruct_csp" ident : tactic
syntax "auto_solve" : tactic
syntax "solve_all_constraints" : tactic

macro_rules
  | `(tactic| all_ren $test:ident $inj:ident $curr:num $goal:num) => do
      let suf := "_" ++ toString curr.getNat
      let mk (s : String) : TSyntax `ident := mkIdent (Name.str .anonymous (s ++ suf))
      let eId := mk "e"
      let currVal := (curr.getNat)
      let currNextVal := (curr.getNat + 1)
      let currNextValSyntax := Syntax.mkNumLit (toString currNextVal)
      let goalVal := (goal.getNat)
      if currVal < goalVal then
        `(tactic|
          have $(eId):ident := ren_label_injective shift_injective _ _ $test:ident;
          all_ren $(eId):ident $inj:ident $currNextValSyntax $goal:num)
      else
        `(tactic|
          try rw [<- $test:ident] at $inj:ident)
  | `(tactic| solve_phi_validation $lemma_phi:ident) => `(tactic|
      intros pm vpm;
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      have tester'' : forall l, L.leq l l = true := L.leq_refl;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label, Owl.ren_label];
      unfold $lemma_phi:ident at vpm;
      simp at vpm;
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| attempt_solve) => `(tactic|
      intros pm vpm;
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      have tester'' : forall l, L.leq l l = true := L.leq_refl;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label, interp_lattice, Owl.ren_label];
      try grind
    )
  | `(tactic| solve_phi_validation_anon) => `(tactic|
      intros pm vpm;
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      have tester'' : forall l, L.leq l l = true := L.leq_refl;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label, Owl.ren_label];
      simp at vpm;
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| solve_phi_validation_anon_no_simp) => `(tactic|
      intros pm vpm;
      have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
      have tester' : forall l, L.leq L.bot l = true := L.bot_all;
      have tester'' : forall l, L.leq l l = true := L.leq_refl;
      unfold phi_map_holds;
      unfold valid_constraint;
      simp [subst_label, Owl.ren_label];
      unfold pcons at vpm;
      case_phi vpm vpm vpm 1 0
    )
  | `(tactic| case_phi $H:ident $A:ident $prevHold:ident $k:num $iter:num) => do
      let suf := "_" ++ toString k.getNat
      let iterVal := (iter.getNat)
      let newKVal := (k.getNat + 1)
      let prevKVal := (k.getNat - 1)
      let prevKValSyntax := Syntax.mkNumLit (toString prevKVal)
      let newIterVal := (iter.getNat + 1)
      let newIterSyntax := Syntax.mkNumLit (toString newIterVal)
      let newKSyntax := Syntax.mkNumLit (toString newKVal)
      let mk (s : String) : TSyntax `ident := mkIdent (Name.str .anonymous (s ++ suf))
      let lId         := mk "l"
      let pmPrevId    := mk "pm_prev"
      let pctxPrevId  := mk "phictx_prev"
      let phiEqId     := mk "phi_eq"
      let symId       := mk "sym"
      let labId       := mk "lab"
      let labValId    := mk "lab_val"
      let tailId      := mk "vpm_tail"
      let headHoldsId := mk "head_holds"
      let aId       := mk "a"
      let hId := mk "h0"
      let labeqId := mk "lab_eq"
      if iterVal = 0 then
        `(tactic|
          first
          | cases $H:ident with
            | phi_empty_valid =>
              try simp at *
              try grind [interp_lattice]
          | cases $H:ident with
            | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                      $(symId):ident $(labId):ident $(labValId):ident
                      $(tailId):ident $(headHoldsId):ident $(aId):ident =>
                have h0 := congrArg (fun f => f 0) $(aId):ident
                simp [lift_phi, cons] at h0
                obtain ⟨sym_eq, lab_eq⟩ := h0
                unfold phi_map_holds at $(headHoldsId):ident
                unfold valid_constraint at $(headHoldsId):ident
                rw [<- lab_eq] at $(headHoldsId):ident
                try simp [ren_label, shift, cons, subst_label, Owl.ren_label] at $(headHoldsId):ident
                simp [var_zero] at $(headHoldsId):ident
                case_phi $(tailId):ident $(aId):ident $(headHoldsId):ident $newKSyntax $newIterSyntax
        )
      else
        `(tactic|
         first
          | cases $H:ident with
            | phi_empty_valid =>
              try simp at *
              try grind [interp_lattice]
          | cases $H:ident with
            | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                      $(symId):ident $(labId):ident $(labValId):ident
                      $(tailId):ident $(headHoldsId):ident $(aId):ident =>
              rw [$(aId):ident] at $A:ident
              have $(hId):ident := congrArg (fun f => f $prevKValSyntax) $A:ident
              simp [lift_phi, cons] at $(hId):ident
              try obtain ⟨sym_eq, $(labeqId):ident⟩ := $(hId):ident
              unfold phi_map_holds at $(headHoldsId):ident
              unfold valid_constraint at $(headHoldsId):ident
              try all_ren $(labeqId):ident $(headHoldsId):ident 0 $prevKValSyntax:num
              try simp [ren_label, shift, cons, subst_label ,Owl.ren_label] at $(headHoldsId):ident
              simp [var_zero] at $(headHoldsId):ident
              try case_phi $(tailId):ident $(A):ident $(headHoldsId):ident $newKSyntax $newIterSyntax
        )
  | `(tactic| case_phi_corr $H:ident $A:ident $prevHold:ident $Csp:ident $k:num $iter:num) => do
      let suf := "_" ++ toString k.getNat
      let iterVal := (iter.getNat)
      let newKVal := (k.getNat + 1)
      let prevKVal := (k.getNat - 1)
      let prevKValSyntax := Syntax.mkNumLit (toString prevKVal)
      let newIterVal := (iter.getNat + 1)
      let newIterSyntax := Syntax.mkNumLit (toString newIterVal)
      let newKSyntax := Syntax.mkNumLit (toString newKVal)
      let mk (s : String) : TSyntax `ident := mkIdent (Name.str .anonymous (s ++ suf))
      let lId         := mk "l"
      let pmPrevId    := mk "pm_prev"
      let pctxPrevId  := mk "phictx_prev"
      let phiEqId     := mk "phi_eq"
      let symId       := mk "sym"
      let labId       := mk "lab"
      let labValId    := mk "lab_val"
      let tailId      := mk "vpm_tail"
      let headHoldsId := mk "head_holds"
      let aId       := mk "a"
      let hId := mk "h0"
      let labeqId := mk "lab_eq"
      if iterVal = 0 then
        `(tactic|
          first
          | cases $H:ident with
            | phi_empty_valid =>
                destruct_csp $Csp:ident
          | cases $H:ident with
            | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                      $(symId):ident $(labId):ident $(labValId):ident
                      $(tailId):ident $(headHoldsId):ident $(aId):ident =>
                have h0 := congrArg (fun f => f 0) $(aId):ident
                simp [lift_phi, cons] at h0
                obtain ⟨sym_eq, lab_eq⟩ := h0
                unfold phi_map_holds at $(headHoldsId):ident
                unfold valid_constraint at $(headHoldsId):ident
                rw [<- lab_eq] at $(headHoldsId):ident
                try simp [ren_label, shift, cons, subst_label, Owl.ren_label] at $(headHoldsId):ident
                simp [var_zero] at $(headHoldsId):ident
                try case_phi_corr $(tailId):ident $(aId):ident $(headHoldsId):ident $Csp:ident $newKSyntax $newIterSyntax
        )
      else
        `(tactic|
          first
          | cases $H:ident with
            | phi_empty_valid =>
                destruct_csp $Csp:ident
          | cases $H:ident with
              | phi_cons $(lId):ident $(pmPrevId):ident $(pctxPrevId):ident $(phiEqId):ident
                        $(symId):ident $(labId):ident $(labValId):ident
                        $(tailId):ident $(headHoldsId):ident $(aId):ident =>
                rw [$(aId):ident] at $A:ident
                have $(hId):ident := congrArg (fun f => f $prevKValSyntax) $A:ident
                simp [lift_phi, cons] at $(hId):ident
                try obtain ⟨sym_eq, $(labeqId):ident⟩ := $(hId):ident
                simp at $(headHoldsId):ident
                unfold phi_map_holds at $(headHoldsId):ident
                unfold valid_constraint at $(headHoldsId):ident
                try all_ren $(labeqId):ident $(headHoldsId):ident 0 $prevKValSyntax:num
                try all_ren $(hId):ident $(headHoldsId):ident 0 $prevKValSyntax:num
                try simp [ren_label, shift, cons, subst_label, Owl.ren_label] at $(headHoldsId):ident
                simp [var_zero] at $(headHoldsId):ident
                try simp [cons] at $(prevHold):ident
                try simp [Owl.cons]
                try simp [cons]
                try case_phi_corr $(tailId):ident $(A):ident $(headHoldsId):ident $Csp:ident $newKSyntax $newIterSyntax
        )
  | `(tactic| destruct_csp $Csp:ident) => do
    `(tactic|
      first
      |   cases $Csp:ident with
          | psi_empty =>
            first
            | trivial
            | (contradiction; trace "contradiction found")
            | grind
      |  cases $Csp:ident with
         | psi_corr psi C' l $Csp:ident Csp' =>
           try simp [Owl.cons] at Csp';
           first
           | (contradiction; trace "contradiction found")
           | destruct_csp $Csp:ident
      | (cases $Csp:ident with
         | psi_not_corr psi C' l $Csp:ident Csp' =>
           try simp [Owl.cons] at Csp';
           first
           | (contradiction; trace "contradiction found")
           | destruct_csp $Csp:ident)
    )
  | `(tactic| check_corr $vpm:ident $C:ident $Csp:ident) => do
    `(tactic|
      first
      | unfold pcons at $vpm:ident;
        have h1 := ($C:ident).has_bot;
        have h2 := ($C:ident).downward_closed;
        have h3 := Owl.L.leq_trans;
        have h4 := Owl.L.bot_all;
        have h5 := Owl.L.leq_refl;
        simp [subst_psi_context, subst_corruption, Owl.subst_label, Owl.ren_label];
        simp [subst_psi_context, subst_corruption, Owl.subst_label, Owl.ren_label] at $Csp:ident;
        (repeat constructor);
        case_phi_corr $vpm:ident $vpm:ident $vpm:ident $Csp:ident 1 0;
      | have h1 := ($C:ident).has_bot;
        have h2 := ($C:ident).downward_closed;
        have h3 := Owl.L.leq_trans;
        have h4 := Owl.L.bot_all;
        have h5 := Owl.L.leq_refl;
        simp [subst_psi_context, subst_corruption, Owl.subst_label, Owl.ren_label];
        simp [subst_psi_context, subst_corruption, Owl.subst_label, Owl.ren_label] at $Csp:ident;
        (repeat constructor);
        case_phi_corr $vpm:ident $vpm:ident $vpm:ident $Csp:ident 1 0;
    )
  | `(tactic| solve_all_constraints) => `(tactic|
      repeat (first
      | constructor <;> (first
          | trivial
          | simp
          | (right; intro pm C vpm Csp; check_corr vpm C Csp)
          | (left; intro pm C vpm Csp; check_corr vpm C Csp)
          | (intro pm C vpm Csp; check_corr vpm C Csp)
          | attempt_solve
          | solve_phi_validation_anon
          | solve_phi_validation_anon_no_simp)))
  | `(tactic| auto_solve) =>
    `(tactic| first
      | intro pm C vpm Csp; check_corr vpm C Csp
      | attempt_solve
      | solve_phi_validation_anon
      | solve_phi_validation_anon_no_simp
      | (apply And.intro; all_goals auto_solve))
  | `(tactic| tc_full $Phi $Psi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Psi $Delta $Gamma $e (some $t) with
      | some result =>
          cases result with
          | mk resty result2 =>
            cases result2 with
            | mk heq result3 =>
              cases result3 with
                | mk side_condition side_condition_sound =>
                  cases h
                  try dsimp at side_condition_sound
                  apply side_condition_sound
                  trace_state;
                  try auto_solve;
                  try simp;
                  $k
      | none =>
          dsimp [infer] at h
          cases h
    )
  | `(tactic| tc_full_man $Phi $Psi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Psi $Delta $Gamma $e (some $t) with
      | some result =>
          cases result with
          | mk resty result2 =>
            cases result2 with
            | mk heq result3 =>
              cases result3 with
                | mk side_condition side_condition_sound =>
                  cases h
                  try dsimp at side_condition_sound
                  apply side_condition_sound
                  trace_state;
                  -- try simp;
                  $k
      | none =>
          dsimp [infer] at h
          cases h
    )

elab_rules : tactic
| `(tactic| tc $k) => do
  let g <- getMainGoal
  let ty <- g.getType
  let args := ty.getAppArgs
  let n := args.size
  let elems := args.extract (n-6) n
  let tac ← `(tactic| tc_full
                $(<- Term.exprToSyntax elems[0]!)
                $(<- Term.exprToSyntax elems[1]!)
                $(<- Term.exprToSyntax elems[2]!)
                $(<- Term.exprToSyntax elems[3]!)
                $(<- Term.exprToSyntax elems[4]!)
                $(<- Term.exprToSyntax elems[5]!)
                $k)
  evalTactic tac
| `(tactic| tc_man $k) => do
  let g <- getMainGoal
  let ty <- g.getType
  let args := ty.getAppArgs
  let n := args.size
  let elems := args.extract (n-6) n
  let tac ← `(tactic| tc_full_man
                $(<- Term.exprToSyntax elems[0]!)
                $(<- Term.exprToSyntax elems[1]!)
                $(<- Term.exprToSyntax elems[2]!)
                $(<- Term.exprToSyntax elems[3]!)
                $(<- Term.exprToSyntax elems[4]!)
                $(<- Term.exprToSyntax elems[5]!)
                $k)
  evalTactic tac
| `(tactic| auto_solve_fast) => do
  let goal ← getMainGoal
  let goalType ← goal.getType'
  if goalType.isAppOfArity ``phi_entails_c 2 then
    evalTactic (← `(tactic| first
      | attempt_solve
      | solve_phi_validation_anon
      | solve_phi_validation_anon_no_simp))
  else if goalType.isAppOfArity ``phi_psi_entail_corr 3 then
    evalTactic (← `(tactic| (intro pm C vpm Csp; check_corr vpm C Csp)))
  else
    evalTactic (← `(tactic| first
      | (apply And.intro; all_goals auto_solve)
      | attempt_solve
      | solve_phi_validation_anon
      | solve_phi_validation_anon_no_simp))

end OwlTypecheck
