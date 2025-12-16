import OwlLean.TypeChecker.OwlTypecheck

open OwlTypecheck
open Owl

#reduce infer empty_phi (empty_psi 0) empty_delta (cons .Unit empty_gamma) (.var_tm ⟨0, by omega⟩) (.some .Unit)

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (.some (.arr .Unit .Unit))


def packed_unit : tm l d m := .pack .Unit .skip

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.unpack (.annot packed_unit (.ex .Any .Unit)) .skip) (.some .Unit)


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


def lemma_phi :=
  (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))
-- How I'd like to write it : (x, y >= x, z >= y, a >= z)

def lemma_phi2 :=
  (pcons (.geq, .var_label ⟨2, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
         (pcons (.geq, .var_label ⟨0, by omega⟩)
                (pcons (.geq, .latl L.bot) empty_phi))))

-- How I'd like to write it : (x, y >= x, z >= y, a >= x)

def lemma_phi_mix (l1 l2 l3 : L.labels) :=
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
