import OwlLean.TypeChecker.OwlTyping

import Lean
import Std.Data.HashMap
open Lean Elab Meta
open Owl

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

-- Infer performs the dual roles of synthesis and checking
-- This is controlled via the the "exp" argument
-- When supplied with a type, the input term will be checked against "exp"
-- If it typechecks, a proof that the input term has type "exp"
-- If no type is provided, infer will attempt to synthesize the type of the input term
-- If successful, it will return the synthesized type, and a proof that the input term has that type
noncomputable def infer (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (exp : Option (ty l d)) :
          Option (match exp with
                  | .none => ((t : ty l d) × Conditional (has_type Phi Psi Delta Gamma e t))
                  | .some exp' => Conditional (has_type Phi Psi Delta Gamma e exp')) :=
  match e with
  | .var_tm x =>
    match exp with
    | .none =>
        let proof := fun _ => has_type.T_Var x
        .some ⟨(Gamma x), ⟨True, proof⟩⟩
    | .some t =>
      let et1 := (Gamma x)
      let et2 := has_type.T_Var x
      let es := check_subtype 99 Phi Psi Delta (Gamma x) t
      match es with
      | .some es' =>
        .some ⟨es'.side_condition, fun sc => has_type.T_Sub (.var_tm x) et1 t (grind es') et2⟩
      | .none => .some ⟨(et1 = t),
          fun h => h ▸ has_type.T_Var x⟩
  | .skip =>
    match exp with
    | .none => .some ⟨.Unit, ⟨True, fun _ => has_type.T_IUnit⟩⟩
    | .some t =>
      match (check_subtype 99 Phi Psi Delta .Unit t) with
      | .some pf =>
        .some ⟨pf.side_condition,
              fun sc =>
                has_type.T_Sub .skip .Unit t (pf.side_condition_sound sc) has_type.T_IUnit⟩
      | .none =>
        .none
  | .bitstring b =>
    match exp with
    | .none => .some ⟨.Public, ⟨True, fun _ => has_type.T_Const b⟩⟩
    | .some t =>
      match (check_subtype 99 Phi Psi Delta .Public t) with
      | .some pf =>
        .some ⟨pf.side_condition,
               fun sc => has_type.T_Sub (.bitstring b) .Public t (pf.side_condition_sound sc) (has_type.T_Const b)⟩
      | .none => .none
  | .Op op e1 e2 => -- This case is long! Might need a step by step.
    match exp with
    | .none => -- try to synthesize
      match infer Phi Psi Delta Gamma e1 .none with -- find type of e1
      | .some ⟨.Data l1, pf1⟩ =>
        match infer Phi Psi Delta Gamma e2 (.some (.Data l1)) with
        | .some e2pf =>
          .some ⟨.Data l1,
                 ⟨pf1.side_condition /\ e2pf.side_condition,
                  fun sc => has_type.T_Op op e1 e2 l1 (pf1.side_condition_sound (by grind)) (e2pf.side_condition_sound (by grind))⟩⟩
        | .none =>
          match infer Phi Psi Delta Gamma e2 .none with  -- find type of e2
          | .some ⟨.Data l2, pf2⟩ =>
            match infer Phi Psi Delta Gamma e1 (.some (.Data l2)) with
            | .some e1pf =>
              .some ⟨.Data l2,
                     ⟨e1pf.side_condition /\ pf2.side_condition,
                      fun sc => has_type.T_Op op e1 e2 l2 (e1pf.side_condition_sound (by grind)) (pf2.side_condition_sound (by grind))⟩⟩
            | .none => .none
          | .some ⟨.Public, pf2⟩ =>
            match infer Phi Psi Delta Gamma e1 (.some .Public) with
            | .some e1pf =>
              .some ⟨.Data (.latl L.bot),
                 ⟨pf2.side_condition /\ e1pf.side_condition,
                  fun sc =>
                  (has_type.T_Op op e1 e2 (.latl L.bot)
                                          (has_type.T_Sub e1 .Public (.Data (.latl L.bot))
                                                                     (subtype.ST_RPublic (.latl L.bot))
                                                                     (e1pf.side_condition_sound (by grind)))
                                          (has_type.T_Sub e2 .Public (.Data (.latl L.bot))
                                                                     (subtype.ST_RPublic (.latl L.bot))
                                                                     (pf2.side_condition_sound (by grind))))⟩⟩
            | .none => .none
          | _ => .none
      | .some ⟨.Public, pf1⟩ =>
        match infer Phi Psi Delta Gamma e2 (.some .Public) with
        | .some e2pf =>
          .some ⟨.Data (.latl L.bot),
                 ⟨pf1.side_condition /\ e2pf.side_condition,
                  fun sc =>
                  (has_type.T_Op op e1 e2 (.latl L.bot)
                                          (has_type.T_Sub e1 .Public (.Data (.latl L.bot))
                                                                     (subtype.ST_RPublic (.latl L.bot))
                                                                     (pf1.side_condition_sound (by grind)))
                                          (has_type.T_Sub e2 .Public (.Data (.latl L.bot))
                                                                     (subtype.ST_RPublic (.latl L.bot))
                                                                     (e2pf.side_condition_sound (by grind))))⟩⟩
        | .none => .none --match on e2, do the whole thing here
      | _ => .none
    | .some t =>
      match t with
      | .Data l =>
        match infer Phi Psi Delta Gamma e1 (.some (.Data l)) with
        | .some pf1 =>
          match infer Phi Psi Delta Gamma e2 (.some (.Data l)) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_Op op e1 e2 l (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | .Public =>
        match infer Phi Psi Delta Gamma e1 (.some .Public) with
        | .some pf1 =>
          match infer Phi Psi Delta Gamma e2 (.some .Public) with
          | .some pf2 =>
            match (check_subtype 99 Phi Psi Delta (.Data (.latl L.bot)) .Public) with -- a bit of a pain to get this to work, but it does (?)
            | .some sub =>
              .some ⟨sub.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                      fun sc => has_type.T_Sub (.Op op e1 e2) (.Data (.latl L.bot)) .Public
                                (grind sub)
                                (has_type.T_Op op e1 e2 (.latl L.bot)
                                              (has_type.T_Sub e1 .Public (.Data (.latl L.bot)) (subtype.ST_RPublic (.latl L.bot)) (grind pf1))
                                              (has_type.T_Sub e2 .Public (.Data (.latl L.bot)) (subtype.ST_RPublic (.latl L.bot)) (grind pf2)))⟩
            | .none => .none
          | .none => .none
        | .none => .none
      | _ => .none
  | .zero e =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
            .some ⟨.Public,
                   ⟨pf.side_condition, fun sc => has_type.T_Zero e l (pf.side_condition_sound (by grind))⟩⟩
      | .some ⟨.Public, pf⟩ =>
        match check_subtype 99 Phi Psi Delta .Public (.Data (.latl L.bot)) with
        | .some sub =>
            .some ⟨.Public,
                   ⟨sub.side_condition /\ pf.side_condition,
                   fun sc => has_type.T_Zero e (.latl L.bot) (has_type.T_Sub e .Public (.Data (.latl L.bot)) (grind sub)
                   (pf.side_condition_sound (by grind)))⟩⟩
        | .none => .none
      | _ => .none
    | .some t =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.Data l, pf⟩ =>
        match check_subtype 99 Phi Psi Delta .Public t with
        | .some sub =>
          .some ⟨pf.side_condition /\ sub.side_condition,
                fun sc => has_type.T_Sub (.zero e) .Public t (grind sub) (has_type.T_Zero e l (grind pf))⟩
        | .none => .none
      | .some ⟨.Public, pf⟩ =>
        match check_subtype 99 Phi Psi Delta .Public t with
        | .some sub =>
          match check_subtype 99 Phi Psi Delta .Public (.Data (.latl L.bot)) with
          | .some sub' =>
            .some ⟨pf.side_condition /\ sub.side_condition /\ sub'.side_condition,
                  fun sc => has_type.T_Sub (.zero e) .Public t (grind sub) (has_type.T_Zero e (.latl L.bot)
                  (has_type.T_Sub e .Public (.Data (.latl L.bot)) (grind sub') (grind pf)))⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .if_tm e e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e (.some .Public) with
      | .some cond_pf =>
        match infer Phi Psi Delta Gamma e1 .none with
        | .some ⟨t1, pf1⟩ =>
          match infer Phi Psi Delta Gamma e2 (.some t1) with
          | .some pf2 =>
            .some ⟨t1,
                  ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                   fun sc => has_type.T_If e e1 e2 t1 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
          | .none =>
            match infer Phi Psi Delta Gamma e2 .none with
            | .some ⟨t2, pf2⟩ =>
              match infer Phi Psi Delta Gamma e1 (.some t2) with
              | .some pf1 =>
                .some ⟨t2, ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition,
                       fun sc => has_type.T_If e e1 e2 t2 (grind cond_pf) (grind pf1) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some t =>
      match infer Phi Psi Delta Gamma e (.some .Public) with
      | .some cond_pf =>
        match infer Phi Psi Delta Gamma e1 (.some t) with
        | .some pf1 =>
          match infer Phi Psi Delta Gamma e2 (.some t) with
          | .some pf2 =>
            .some ⟨cond_pf.side_condition /\ pf1.side_condition /\ pf2.side_condition ,
                    fun sc => has_type.T_If e e1 e2 t (grind cond_pf) (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .alloc e =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨t, pf⟩ =>
        .some ⟨.Ref t, ⟨pf.side_condition, fun sc =>has_type.T_IRef e t (grind pf)⟩⟩
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .Ref t =>
        match infer Phi Psi Delta Gamma e (.some t) with
        | .some pf => .some ⟨pf.side_condition, fun sc => has_type.T_IRef e t (grind pf)⟩
        | .none => .none
      | _ => .none
  | .dealloc e =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.Ref t, pf⟩ =>
        .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_ERef e t (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e (.some (.Ref exp_ty)) with
      | .some pf => .some ⟨pf.side_condition , fun sc => has_type.T_ERef e exp_ty (grind pf)⟩
      | .none => .none
  | .assign e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e1 .none with
      | .some ⟨.Ref t, pf1⟩ =>
        match infer Phi Psi Delta Gamma e2 (.some t) with
        | .some pf2 =>
          .some ⟨.Unit, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_Assign e1 e2 t (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match exp_ty with
      | .Unit =>
        match infer Phi Psi Delta Gamma e1 .none with
        | .some ⟨.Ref t, pf1⟩ =>
          match infer Phi Psi Delta Gamma e2 (.some t) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_Assign e1 e2 t (grind pf1) (grind pf2)⟩
          | .none => .none
        | _ => .none
      | _ => .none
  | .inl e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort! (No need to add right now)
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer Phi Psi Delta Gamma e (.some t1) with
        | .some pr => .some ⟨pr.side_condition, fun sc => has_type.T_ISumL e t1 t2 (grind pr)⟩
        | .none => .none
      | _ => .none
  | .inr e =>
    match exp with
    | .none => .none -- CANNOT synthesize! Abort! Abort! (No need to add right now)
    | .some t =>
      match t with
      | .sum t1 t2 =>
        match infer Phi Psi Delta Gamma e (.some t2) with
        | .some pr => .some ⟨pr.side_condition, fun sc => has_type.T_ISumR e t1 t2 (grind pr)⟩
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
        | .some pe => .some ⟨pe.side_condition, fun sc => has_type.T_IFun e t t' (grind pe)⟩
        | .none => .none
      | _ => .none
  | .app e1 e2 =>
    match exp with
    | .none => -- synthesize
      match infer Phi Psi Delta Gamma e1 .none with
      | .some ⟨ty1, pf1⟩ =>
        match ty1 with
        | .arr t t' =>
          match infer Phi Psi Delta Gamma e2 (.some t) with
          | .some pf2 => .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_EFun e1 e2 t t' (grind pf1) (grind pf2)⟩⟩
          | .none => .none
        | _ => .none
      | .none => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e2 .none with
      | .some ⟨ty1, pf1⟩ =>
        match infer Phi Psi Delta Gamma e1 (.some (.arr ty1 exp_ty)) with
        | .some pf2 =>
          .some ⟨pf1.side_condition /\ pf2.side_condition,
                 fun sc => (has_type.T_EFun e1 e2 ty1 exp_ty (grind pf2) (grind pf1))⟩
        | .none => .none
      | _ => .none
  | .tm_pair e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e1 .none with
      | .some ⟨t1, pf1⟩ =>
        match infer Phi Psi Delta Gamma e2 .none with
        | .some ⟨t2, pf2⟩ =>
          .some ⟨.prod t1 t2, ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩⟩
        | .none => .none
      | .none => .none
    | .some exp_ty =>
      match exp_ty with
      | .prod t1 t2 =>
        match infer Phi Psi Delta Gamma e1 (.some t1) with
        | .some pf1 =>
          match infer Phi Psi Delta Gamma e2 (.some t2) with
          | .some pf2 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition, fun sc => has_type.T_IProd e1 e2 t1 t2 (grind pf1) (grind pf2)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .left_tm e =>
    match exp with
    | .none => -- synthesize
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t1, ⟨pf.side_condition, fun sc => has_type.T_EProdL e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype 99 Phi Psi Delta t1 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition ,
                 fun sc => has_type.T_Sub (.left_tm e) t1 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdL e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .right_tm e =>
    match exp with
    | .none => -- synthesize
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        .some ⟨t2, ⟨pf.side_condition, fun sc => has_type.T_EProdR e t1 t2 (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.prod t1 t2, pf⟩ =>
        match check_subtype 99 Phi Psi Delta t2 exp_ty with
        | .some sub_pf =>
          .some ⟨pf.side_condition /\ sub_pf.side_condition,
                 fun sc => has_type.T_Sub (.right_tm e) t2 exp_ty (grind sub_pf)
                                                                 (has_type.T_EProdR e t1 t2 (grind pf))⟩
        | .none => .none
      | _ => .none
  | .case e e1 e2 =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer Phi Psi Delta (cons t1 Gamma) e1 .none with
        | .some ⟨t, pf2⟩ =>
          match infer Phi Psi Delta (cons t2 Gamma) e2 (.some t) with
          | .some pf3 =>
            .some ⟨t, ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                       fun sc =>
                         has_type.T_ESum e t1 t2 t e1 e2 (grind pf1) (grind pf2) (grind pf3)⟩⟩
          | .none =>
            match infer Phi Psi Delta (cons t2 Gamma) e2 .none with
            | .some ⟨t', pf2⟩ =>
              match infer Phi Psi Delta (cons t1 Gamma) e1 (.some t') with
              | .some pf3 =>
                .some ⟨t', ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                            fun sc =>
                              has_type.T_ESum e t1 t2 t' e1 e2 (grind pf1) (grind pf3) (grind pf2)⟩⟩
              | .none => .none
            | .none => .none
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.sum t1 t2, pf1⟩ =>
        match infer Phi Psi Delta (cons t1 Gamma) e1 (.some exp_ty) with
        | .some pf2 =>
          match infer Phi Psi Delta (cons t2 Gamma) e2 (.some exp_ty) with
          | .some pf3 =>
            .some ⟨pf1.side_condition /\ pf2.side_condition /\ pf3.side_condition,
                  fun sc => has_type.T_ESum e t1 t2 exp_ty e1 e2 (grind pf1) (grind pf2) (grind pf3)⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .tlam e =>
    match exp with
    | .none => .none  -- TODO : Synthesize!!!
    | .some (.all t0 t) =>
      match infer Phi Psi (lift_delta (cons t0 Delta)) (lift_gamma_d Gamma) e (.some t) with
      | .some pf =>
        .some ⟨pf.side_condition,
                   fun sc => has_type.T_IUniv t0 t e (grind pf)⟩
      | .none => .none
    | _ => .none
  | .tapp e t' =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf1⟩ =>
        let sub := check_subtype 99 Phi Psi Delta t' t0
        match sub with
        | .some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
         .some ⟨result_ty,
                  ⟨pf1.side_condition /\ sub'.side_condition,
                  fun sc => has_type.T_EUniv t t' t0 e (grind sub') (grind pf1)⟩⟩
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all t0 t, pf⟩ =>
        let sub := check_subtype 99 Phi Psi Delta t' t0
        match sub with
        | some sub' =>
          let result_ty := subst_ty .var_label (cons t' .var_ty) t
          let sub_result := check_subtype 99 Phi Psi Delta result_ty exp_ty
          match sub_result with
          | .some sub_result' =>
            .some ⟨pf.side_condition /\ sub'.side_condition /\ sub_result'.side_condition,
                      fun sc =>
                        has_type.T_Sub (.tapp e t') result_ty exp_ty (grind sub_result')
                          (has_type.T_EUniv t t' t0 e (grind sub') (grind pf))⟩
          | .none => .none
        | .none => .none
      | _ => .none
  | .pack t' e =>
    match exp with
    | .none => .none -- TODO : potentially ADD Synthesis!
    | .some (.ex t0 t) =>
      let substituted_type := subst_ty .var_label (cons t' .var_ty) t
      match check_subtype 99 Phi Psi Delta t' t0 with
      | .some sub =>
        match infer Phi Psi Delta Gamma e (.some substituted_type) with
        | .some pf =>
          .some ⟨pf.side_condition /\ sub.side_condition,
                 fun sc => has_type.T_IExist e t t' t0 (grind pf) (grind sub)⟩
        | .none => .none
      | .none => .none
    | _ => .none
  | .unpack e e' =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.ex t0 t, pf_e⟩ =>
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        match infer Phi Psi extended_delta extended_gamma e' .none with
        | .some ⟨t', pf_e'⟩ =>
          .none -- TODO TEMP FOR NOW ; NEEDS UNSHIFTING; SEEMINGLY CANNOT BE DONE OTHERWISE
        | .none => .none
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.ex t0 t, pf_e⟩ =>
        let extended_delta := lift_delta (cons t0 Delta)
        let extended_gamma := cons t (lift_gamma_d Gamma)
        let renamed_t' := ren_ty id shift exp_ty
        match infer Phi Psi extended_delta extended_gamma e' (.some renamed_t') with
        | .some pf_e' =>
                .some ⟨pf_e.side_condition /\ pf_e'.side_condition,
                       fun sc => has_type.T_EExist e e' t0 t exp_ty (grind pf_e) (grind pf_e')⟩
        | .none => .none
      | _ => .none
  | .l_lam e =>
    match exp with
    | .none => .none -- TODO NEED SYNTHESIS LATER (SUPPLY BOUND)
    | .some exp_ty =>
      match exp_ty with
      | .all_l cs lab t_body =>
         match infer (lift_phi ((cons (cs, lab)) Phi))
                  (lift_psi Psi)
                  (lift_delta_l Delta) (lift_gamma_l Gamma)
                  e (.some t_body) with
         | .some pe =>
           .some ⟨pe.side_condition,
               fun sc => has_type.T_ILUniv cs lab e t_body (grind pe)⟩
         | .none => .none
      | _ => .none
  | .lapp e lab' =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, pf⟩ =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        let constraint_obligation := (Phi |= (.condition cs lab lab'))
        .some ⟨result_ty,
              ⟨pf.side_condition /\ constraint_obligation,
                fun sc =>
                  has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf)⟩⟩
      | _ => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e .none with
      | .some ⟨.all_l cs lab t, pf⟩ =>
        let result_ty := subst_ty (cons lab' .var_label) .var_ty t
        match check_subtype 99 Phi Psi Delta result_ty exp_ty with
        | .some sub_pf =>
          let constraint_obligation := (Phi |= (.condition cs lab lab'))
          .some ⟨pf.side_condition /\ constraint_obligation /\ sub_pf.side_condition,
                fun sc =>
                  has_type.T_Sub (.lapp e lab') result_ty exp_ty
                    (grind sub_pf)
                    (has_type.T_ELUniv cs lab lab' e t (by grind) (grind pf))⟩
        | .none => .none
      | _ => .none
  | .annot e t' => -- LONG CASE TO HANDLE IF CHECKING PROPERLY
    match exp with
    | .none =>
      match t' with
      | .t_if lab t1 t2 =>
        match infer Phi ((.corr lab) :: Psi) Delta Gamma e (.some t1),
              infer Phi ((.not_corr lab) :: Psi) Delta Gamma e (.some t2) with
        | .some pf1, .some pf2 =>
          .some ⟨ty.t_if lab t1 t2,
                ⟨pf1.side_condition /\ pf2.side_condition,
                 fun sc =>
                   has_type.T_Annot e (ty.t_if lab t1 t2)
                     (derived_if_typing_annot lab e
                       (pf1.side_condition_sound sc.left)
                       (pf2.side_condition_sound sc.right))⟩⟩
        | _, _ =>
          match infer Phi Psi Delta Gamma e (.some t1),
                infer Phi Psi Delta Gamma e (.some t2) with
          | .some pf1, .none =>
            let corr_cond := phi_psi_entail_corr Phi Psi (.corr lab)
            .some ⟨ty.t_if lab t1 t2,
                  ⟨pf1.side_condition /\ corr_cond,
                   fun sc =>
                     has_type.T_Annot e (ty.t_if lab t1 t2)
                       (has_type.T_Sub e t1 (ty.t_if lab t1 t2)
                         (subtype.ST_RIf1 lab t1 t1 t2 sc.right (subtype.ST_Refl t1))
                         (pf1.side_condition_sound sc.left))⟩⟩
          | .none, .some pf2 =>
            let not_corr_cond := phi_psi_entail_corr Phi Psi (.not_corr lab)
            .some ⟨ty.t_if lab t1 t2,
                  ⟨pf2.side_condition /\ not_corr_cond,
                   fun sc =>
                     has_type.T_Annot e (ty.t_if lab t1 t2)
                       (has_type.T_Sub e t2 (ty.t_if lab t1 t2)
                         (subtype.ST_RIf2 lab t2 t1 t2 sc.right (subtype.ST_Refl t2))
                         (pf2.side_condition_sound sc.left))⟩⟩
          | _, _ => .none
      | t => -- NORMAL CASE FOR SYNTHESIZING
        match infer Phi Psi Delta Gamma e (.some t) with
        | .some pf => .some ⟨t, ⟨pf.side_condition, fun sc => has_type.T_Annot e t (pf.side_condition_sound sc)⟩⟩
        | .none => .none
    | .some exp_ty => -- Check the type of annotation
      match t' with
      | .t_if lab t1 t2 =>
        match infer Phi ((.corr lab) :: Psi) Delta Gamma e (.some t1),
              infer Phi ((.not_corr lab) :: Psi) Delta Gamma e (.some t2) with
        | .some pf1, .some pf2 =>
          match check_subtype 99 Phi Psi Delta (ty.t_if lab t1 t2) exp_ty with
          | .some sub =>
            .some ⟨pf1.side_condition /\ pf2.side_condition /\ sub.side_condition,
                  fun sc =>
                    has_type.T_Sub (.annot e (ty.t_if lab t1 t2)) (ty.t_if lab t1 t2) exp_ty
                      (sub.side_condition_sound sc.right.right)
                      (has_type.T_Annot e (ty.t_if lab t1 t2)
                        (derived_if_typing_annot lab e
                          (pf1.side_condition_sound sc.left)
                          (pf2.side_condition_sound sc.right.left)))⟩
          | .none => .none
        | _, _ =>
          match infer Phi Psi Delta Gamma e (.some t1),
                infer Phi Psi Delta Gamma e (.some t2) with
          | .some pf1, .none =>
            let corr_cond := phi_psi_entail_corr Phi Psi (.corr lab)
            match check_subtype 99 Phi Psi Delta (ty.t_if lab t1 t2) exp_ty with
            | .some sub =>
              .some ⟨pf1.side_condition ∧ corr_cond ∧ sub.side_condition,
                    fun sc =>
                      has_type.T_Sub (.annot e (ty.t_if lab t1 t2)) (ty.t_if lab t1 t2) exp_ty
                        (sub.side_condition_sound sc.right.right)
                        (has_type.T_Annot e (ty.t_if lab t1 t2)
                          (has_type.T_Sub e t1 (ty.t_if lab t1 t2)
                            (subtype.ST_RIf1 lab t1 t1 t2 sc.right.left (subtype.ST_Refl t1))
                            (pf1.side_condition_sound sc.left)))⟩
            | .none => .none
          | .none, .some pf2 =>
            let not_corr_cond := phi_psi_entail_corr Phi Psi (.not_corr lab)
            match check_subtype 99 Phi Psi Delta (ty.t_if lab t1 t2) exp_ty with
            | .some sub =>
              .some ⟨pf2.side_condition ∧ not_corr_cond ∧ sub.side_condition,
                    fun sc =>
                      has_type.T_Sub (.annot e (ty.t_if lab t1 t2)) (ty.t_if lab t1 t2) exp_ty
                        (sub.side_condition_sound sc.right.right)
                        (has_type.T_Annot e (ty.t_if lab t1 t2)
                          (has_type.T_Sub e t2 (ty.t_if lab t1 t2)
                            (subtype.ST_RIf2 lab t2 t1 t2 sc.right.left (subtype.ST_Refl t2))
                            (pf2.side_condition_sound sc.left)))⟩
            | .none => .none
          | _, _ => .none
      | t => -- NORMAL CASE FOR CHECKING
        match check_subtype 99 Phi Psi Delta t exp_ty with
        | .some sub =>
          match infer Phi Psi Delta Gamma e (.some t) with
          | .some pf =>
            .some ⟨sub.side_condition ∧ pf.side_condition,
                  fun sc => has_type.T_Sub (.annot e t) t exp_ty (grind sub)
                          (has_type.T_Annot e t (grind pf))⟩
          | .none => .none
        | .none => .none
  | .if_c lab e1 e2 =>
    -- synthesis
    let synth :
      Option ((t : ty l d) × Conditional (has_type Phi Psi Delta Gamma (.if_c lab e1 e2) t)) :=
      match infer Phi ((.corr lab) :: Psi) Delta Gamma e1 none,
            infer Phi ((.not_corr lab) :: Psi) Delta Gamma e2 none with
      | some ⟨t1, pf1⟩, some ⟨t2, pf2⟩ =>
          let t := ty.t_if lab t1 t2
          some ⟨t,
            ⟨pf1.side_condition /\ pf2.side_condition,
              fun sc =>
                derived_if_typing lab e1 e2
                  (pf1.side_condition_sound sc.left)
                  (pf2.side_condition_sound sc.right)⟩⟩
      | _, _ =>
        match infer Phi Psi Delta Gamma e1 none,
              infer Phi Psi Delta Gamma e2 none with
        | some ⟨t1, pf1⟩, none =>
            let corr_cond := phi_psi_entail_corr Phi Psi (.corr lab)
            some ⟨t1,
                  ⟨pf1.side_condition /\ corr_cond,
                  fun sc => has_type.T_IfCorr2 lab t1 e1 e2 sc.right
                                              (pf1.side_condition_sound sc.left)⟩⟩
        | none, some ⟨t2, pf2⟩ =>
            let not_corr_cond := phi_psi_entail_corr Phi Psi (.not_corr lab)
            some ⟨t2,
                  ⟨pf2.side_condition /\ not_corr_cond,
                  fun sc => has_type.T_IfCorr1 lab t2 e1 e2 sc.right
                                              (pf2.side_condition_sound sc.left)⟩⟩
        | _, _ => none
    match exp, synth with
    | none, r => r
    | some t, some ⟨t', pft⟩ =>
        match check_subtype 99 Phi Psi Delta t' t with
        | some sub =>
            some
            ⟨pft.side_condition ∧ sub.side_condition,
              fun sc =>
                has_type.T_Sub (.if_c lab e1 e2) t' t
                  (sub.side_condition_sound sc.right)
                  (pft.side_condition_sound sc.left)⟩
        | none => none
    | _, _ => none
  | .corr_case lab e =>
    match exp with
    | .none => -- attempt synthesis
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      match infer Phi psi_corr Delta Gamma e .none, infer Phi psi_not_corr Delta Gamma e .none with
      | .some ⟨t1, pf1⟩, .some ⟨t2, pf2⟩ =>
        match check_subtype 99 Phi psi_corr Delta t1 t2 with
        | .some sub12 =>
          .some ⟨t2, ⟨pf1.side_condition /\ pf2.side_condition /\ sub12.side_condition,
                    fun sc =>
                      has_type.T_CorrCase lab e t2
                        (has_type.T_Sub e t1 t2 (grind sub12)
                          (grind pf1))
                          (grind pf2)⟩⟩
        | .none =>
          match check_subtype 99 Phi psi_not_corr Delta t2 t1 with
          | .some sub21 =>
            .some ⟨t1, ⟨pf1.side_condition /\ pf2.side_condition /\ sub21.side_condition,
                        fun sc =>
                          has_type.T_CorrCase lab e t1
                            (grind pf1)
                            (has_type.T_Sub e t2 t1 (grind sub21)
                              (grind pf2))⟩⟩
          | .none => .none
      | _, _ => .none
    | .some exp_ty =>
      let psi_corr := (.corr lab) :: Psi
      let psi_not_corr := (.not_corr lab) :: Psi
      match infer Phi psi_corr Delta Gamma e (.some exp_ty), infer Phi psi_not_corr Delta Gamma e (.some exp_ty) with
      | .some pf1, .some pf2 =>
        .some ⟨pf1.side_condition /\ pf2.side_condition,
            fun sc =>
              has_type.T_CorrCase lab e exp_ty
                (grind pf1)
                (grind pf2)⟩
      | _, _ => .none
  | .sync e =>
    match exp with
    | .none =>
      match infer Phi Psi Delta Gamma e (.some .Public) with
      | .some pf1 =>
        .some ⟨.Public, ⟨pf1.side_condition, fun sc => has_type.T_Sync e (grind pf1)⟩⟩
      | .none => .none
    | .some exp_ty =>
      match infer Phi Psi Delta Gamma e (.some .Public) with
      | .some pf1 =>
        match check_subtype 99 Phi Psi Delta .Public exp_ty with
        | .some sub =>
          .some ⟨pf1.side_condition /\ sub.side_condition,
                fun sc => has_type.T_Sub (.sync e) .Public exp_ty
                (grind sub)
                (has_type.T_Sync e (grind pf1))⟩
        | .none => .none
      | .none => .none
  | _ =>
    match exp with
    | .some _ => .none
    | .none => .none
  -- TODO CORR cases for infer and check_subtype (adding corruptions to justify types) (may be done)

theorem infer_sound (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) (t : ty l d) :
          forall cond,
           infer Phi Psi Delta Gamma e (some t) = some cond →
           cond.side_condition →
           has_type Phi Psi Delta Gamma e t := by
  intro cond h1 h2
  simp at cond
  have cond' := cond.side_condition_sound
  apply cond'
  apply h2

theorem infer_sound_none (Phi : phi_context l) (Psi : psi_context l) (Delta : delta_context l d)
          (Gamma : gamma_context l d m) (e : tm l d m) :
  (forall result, infer Phi Psi Delta Gamma e none = some result ->
          result.snd.side_condition ->
          has_type Phi Psi Delta Gamma e result.fst) := by
  intros cond h1 h2
  simp at cond
  have cond' := cond.snd.side_condition_sound
  apply cond'
  apply h2

syntax "tc_full" term:max term:max term:max term:max term:max term:max tactic : tactic
syntax "tc_full_man" term:max term:max term:max term:max term:max term:max tactic : tactic

open Lean Meta Elab Tactic

def simple_test_delta :=
   (dcons .Unit (@empty_delta 0))

def test_delta_2 :=
   (dcons (.var_ty ⟨0, by omega⟩) simple_test_delta)

noncomputable def simple_test_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩) (pcons (.geq, .latl L.bot) empty_phi))

noncomputable def simple_test_gamma : gamma_context 0 0 1 :=
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

syntax "solve_phi_validation" ident : tactic
syntax "attempt_solve" : tactic
syntax "solve_phi_validation_anon" : tactic
syntax "solve_phi_validation_anon_no_simp" : tactic
syntax "case_phi " ident ident ident num num : tactic
syntax "case_phi_corr" ident ident ident ident num num : tactic
syntax "all_ren" ident ident num num : tactic
syntax "check_corr" ident ident ident : tactic
syntax "destruct_csp" ident : tactic

macro_rules
  | `(tactic| all_ren $test:ident $inj:ident $curr:num $goal:num) => do
      let suf := "_" ++ toString curr.getNat
      let mk (s : String) : TSyntax `ident := mkIdent <| Name.str .anonymous (s ++ suf)
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
      let mk (s : String) : TSyntax `ident := mkIdent <| Name.str .anonymous (s ++ suf)
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
      let mk (s : String) : TSyntax `ident := mkIdent <| Name.str .anonymous (s ++ suf)
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

macro "solve_all_constraints" : tactic => `(tactic|
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

syntax "auto_solve" : tactic
macro_rules
  | `(tactic| auto_solve) =>
    `(tactic| first
      | intro pm C vpm Csp; check_corr vpm C Csp
      | attempt_solve
      | solve_phi_validation_anon
      | solve_phi_validation_anon_no_simp
      | (apply And.intro; all_goals auto_solve))

syntax "auto_solve_fast" : tactic

elab "auto_solve_fast" : tactic => do
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

macro_rules
  | `(tactic| tc_full $Phi $Psi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Psi $Delta $Gamma $e (some $t) with
      | some result =>
          cases result with
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

macro_rules
  | `(tactic| tc_full_man $Phi $Psi $Delta $Gamma $e $t $k) => `(tactic|
      cases h : infer $Phi $Psi $Delta $Gamma $e (some $t) with
      | some result =>
          cases result with
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

syntax "tc" tactic:max : tactic
syntax "tc_man" tactic:max : tactic

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

elab_rules : tactic
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

#reduce infer empty_phi (empty_psi 0) empty_delta (cons .Unit empty_gamma) (.var_tm ⟨0, by omega⟩) (.some .Unit)

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.some (.arr .Unit .Unit))

theorem skip_has_unit_type (Phi : phi_context l) (Delta : delta_context l d)
                           (Gamma : gamma_context l d m) :
                           has_type Phi Psi Delta Gamma .skip .Any := by
  cases h : infer Phi Psi Delta Gamma .skip (.some .Any) with
  | some result =>
          dsimp [infer, check_subtype, cons] at h;
          cases result with
          | mk side_condition side_condition_sound =>
            cases h;
            apply side_condition_sound
            grind
  | none =>
          dsimp [infer, check_subtype] at h
          cases h

def packed_unit : tm l d m := .pack .Unit .skip

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.unpack (.annot packed_unit (.ex .Any .Unit)) .skip) (.some .Unit)

-- for label testing purposes!
theorem stub_label_flow : L.leq l1 l2 = true := by
  sorry

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.tm_pair (.alloc .skip) (.bitstring .bend)) (.some (.prod (.Ref .Unit) .Public))

theorem tc_ref_refl (Phi : phi_context l)
                    (Psi : psi_context l)
                    (Delta : delta_context l d) :
  has_type Phi Psi Delta (cons (.Ref (.prod .Unit .Unit)) empty_gamma)
    (tm.var_tm ⟨0, by omega⟩)
    (.Ref (.prod .Unit .Unit)) := by
  tc (try grind)

theorem tc_ref_refl2 (Phi : phi_context l)
                    (Delta : delta_context l d) (l1 : L.labels) :
  has_type Phi Psi Delta (cons (.Ref (.Data (.latl l1))) empty_gamma)
    (tm.var_tm ⟨0, by omega⟩)
    (.Ref (.Data (.latl l1))) := by
  tc (try grind)

theorem tc_prod   (Phi : phi_context l)
                    (Delta : delta_context l d) (Gamma : gamma_context l d m) :
  has_type Phi Psi Delta Gamma
    (.tm_pair (.alloc .skip) (.bitstring .bend))
    (.prod (.Ref .Unit) (.Data (.latl l1))):= by
  tc (try grind)

theorem tc_label (Phi : phi_context l)
                         (Delta : delta_context l d) :
                         has_type Phi Psi Delta (cons (.Data (.latl l1)) empty_gamma)
                         (tm.var_tm ⟨0, by omega⟩)
                         (.Data (.latl l2)) := by
  tc (
    try simp
    try exact stub_label_flow
    try sorry
  )

theorem packed_unit_tc (Phi : phi_context l)
                         (Delta : delta_context l d) (Gamma : gamma_context l d m) :
                         has_type Phi Psi Delta (cons (.Data (.latl l1))  Gamma)
                           packed_unit
                           (.ex .Any .Unit) := by
  tc (try grind)

theorem unpack_packed_skip_alt :
  has_type empty_phi (empty_psi 0)
           (dcons (.var_ty ⟨0, by omega⟩) (dcons .Unit empty_delta)) empty_gamma
           (.tapp
              (.annot (.tlam .skip) (.all .Any .Unit))
              (.var_ty ⟨1, by omega⟩))
           .Unit := by
  tc (try grind)


theorem pack_unit_exists (Phi : phi_context l)
                         (Delta : delta_context l d) (Gamma : gamma_context l d m) :
                         has_type Phi Psi Delta Gamma
                           (.pack .Unit (.tm_pair .skip .skip))
                           (.ex .Any (.prod (.var_ty 0) (.var_ty 0))) := by
  tc (try grind)

theorem lambda_simple (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type Phi Psi Delta Gamma (.fixlam (.alloc .skip)) (.arr .Unit (.Ref .Unit)) := by
  tc (try grind)

theorem lambda_identity_unit (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
          has_type Phi Psi Delta Gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.arr .Unit .Unit) := by
  tc (try grind)

-- Proof that injection into a larger goal works
theorem test_inject : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) /\ True := by
  apply And.intro
  unfold phi_entails_c
  intro pm vpm
  unfold phi_map_holds
  dsimp
  unfold valid_constraint
  dsimp
  simp [interp_lattice]
  have lp : forall (l : L.labels), (L.leq L.bot l) = true := L.bot_proof
  apply (lp l1)
  trivial

theorem test_inject_2 : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) := by
  have ti : (Phi |= constr.condition cond_sym.leq (label.latl L.bot) (label.latl l1)) /\ True :=
    test_inject
  exact ti.left

-- Proof, that you can pass in a proof (proof of proof)
theorem bitstring_has_bot_type (Phi : phi_context l) (Delta : delta_context l d)
                                (Gamma : gamma_context l d m) (b : binary) :
                                has_type Phi Psi Delta Gamma (.bitstring b) (.Data (.latl l1)) := by
  tc (try grind)

-- Test theorem for inl with skip
theorem inl_skip_has_sum_type (Phi : phi_context l) (Delta : delta_context l d)
                              (Gamma : gamma_context l d m) (t2 : ty l d) :
                              has_type Phi Psi Delta Gamma (.inl .skip) (.sum .Unit t2) := by
  tc (try grind)

theorem fixlam_identity (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type Phi Psi Delta Gamma
                          (.fixlam .skip)
                          (.arr .Any .Unit) := by
  tc (try grind)

theorem pair_easy (Phi : phi_context l) (Delta : delta_context l d)
                        (Gamma : gamma_context l d m) :
                        has_type Phi Psi Delta Gamma
                        (.tm_pair .skip .skip)
                        (.prod .Unit .Unit) := by
  tc (try grind)


noncomputable def lemma_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))
-- How I'd like to write it : (x, y >= x, z >= y, a >= z)

noncomputable def lemma_phi2 :=
  (pcons (.geq, .var_label ⟨2, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))

-- How I'd like to write it : (x, y >= x, z >= y, a >= x)

noncomputable def lemma_phi_mix (l1 l2 l3 : L.labels) :=
  (pcons (.geq, (.latl l1))
         (pcons (.geq, (.latl l2))
         (pcons (.geq, (.latl l3))
                (pcons (.geq, .latl L.bot) empty_phi))))

theorem test_latt :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨3, by omega⟩)) := by
    solve_phi_validation lemma_phi

theorem test_latt2 :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨2, by omega⟩)) := by
    solve_phi_validation lemma_phi

theorem test_latt3 :
  lemma_phi2 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨3, by omega⟩)) := by
    solve_phi_validation lemma_phi2

theorem test_latt_mix (l1 l2 l3 : L.labels) (pf1 : L.leq l1 l2 = true) (pf2 : L.leq l2 l3 = true):
  empty_phi |= (.condition .leq (.latl l1) (.latl l3)) := by
    attempt_solve

theorem test_latt_mix2 (l1 l2 l3 : L.labels) :
  lemma_phi_mix l1 l2 l3 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.latl l1)) := by
    solve_phi_validation lemma_phi_mix

-- Tedious example (non tactic)
theorem test_latt_manual :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨2, by omega⟩)) := by
  intros pm vpm;
  have tester : forall l1 l2 l3, L.leq l1 l2 -> L.leq l2 l3 -> L.leq l1 l3 := L.leq_trans;
  have tester' : forall l, L.leq L.bot l = true := L.bot_all;
  have tester'' : forall l, L.leq l l = true := L.leq_refl;
  unfold phi_map_holds;
  unfold valid_constraint;
  simp [subst_label];
  unfold lemma_phi at vpm;
  unfold pcons at vpm;
  cases vpm with
  | phi_cons l1 pm_prev1 phictx_prev1 phi_eq1 sym1 lab1 lab_val1 h_prev1 h_holds1 a1 =>
    have h0 := congrArg (fun f => f 0) a1
    simp [lift_phi, cons] at h0
    obtain ⟨sym_eq, lab_eq⟩ := h0
    unfold phi_map_holds at h_holds1
    unfold valid_constraint at h_holds1
    rw [<- lab_eq] at h_holds1
    try simp [ren_label, shift, cons, subst_label, Owl.ren_label] at h_holds1
    simp [var_zero] at h_holds1
    cases h_prev1 with
    | phi_cons l2 pm_prev2 phictx_prev2 phi_eq2 sym2 lab2 lab_val2 h_prev2 h_holds2 a2 =>
      rw [a2] at a1
      have h0 := congrArg (fun f => f 1) a1
      simp [lift_phi, cons] at h0
      obtain ⟨sym_eq, lab_eq⟩ := h0
      simp at h_holds2
      unfold phi_map_holds at h_holds2
      unfold valid_constraint at h_holds2
      try all_ren lab_eq h_holds2 0 1
      try simp [ren_label, cons, subst_label] at h_holds2
      simp [var_zero] at h_holds2
      cases h_prev2 with
      | phi_cons l3 pm_prev3 phictx_prev3 phi_eq3 sym3 lab3 lab_val3 h_prev3 h_holds3 a3 =>
        rw [a3] at a1
        have h0 := congrArg (fun f => f 2) a1
        simp [lift_phi, cons] at h0
        obtain ⟨sym_eq, lab_eq⟩ := h0
        simp at h_holds3
        unfold phi_map_holds at h_holds3
        unfold valid_constraint at h_holds3
        try all_ren lab_eq h_holds2 0 2
        try simp [cons, subst_label] at h_holds3
        simp [var_zero] at h_holds3
        cases h_prev3 with
        | phi_cons l4 pm_prev4 phictx_prev4 phi_eq4 sym4 lab4 lab_val4 h_prev4 h_holds4 a4 =>
          rw [a4] at a1
          have h0 := congrArg (fun f => f 3) a1
          simp [lift_phi, cons] at h0
          obtain ⟨sym_eq, lab_eq⟩ := h0
          simp at h_holds4
          unfold phi_map_holds at h_holds4
          unfold valid_constraint at h_holds4
          try all_ren lab_eq h_holds2 0 3
          try simp [cons, subst_label] at h_holds4
          simp [var_zero] at h_holds4
          simp at *
          grind [interp_lattice]
