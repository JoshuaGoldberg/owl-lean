import OwlLean.TypeChecker.OwlTypecheck
import OwlLean.OwlLang.Owl

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
    intros p Hp
    simp
    simp [lemma_phi] at *
    simp [Fin.foldr_succ] at Hp
    grind


theorem test_latt2 :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨2, by omega⟩)) := by
    intros p Hp
    simp
    simp [lemma_phi] at *
    simp [Fin.foldr_succ] at Hp
    grind

theorem test_latt3 :
  lemma_phi2 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨3, by omega⟩)) := by
    intros p Hp
    simp
    simp [lemma_phi2] at *
    simp [Fin.foldr_succ] at Hp
    grind


theorem test_latt_mix (l1 l2 l3 : L.labels) (pf1 : L.leq l1 l2 = true) (pf2 : L.leq l2 l3 = true):
  empty_phi |= (.condition .leq (.latl l1) (.latl l3)) := by
    intros p Hp
    simp [empty_phi] at *
    grind

theorem test_latt_mix2 (l1 l2 l3 : L.labels) :
  lemma_phi_mix l1 l2 l3 |= (.condition .geq (.var_label ⟨0, by omega⟩) (.latl l1)) := by
    intros p Hp
    simp [lemma_phi_mix] at *
    simp [Fin.foldr_succ] at Hp
    grind

theorem test_latt_manual :
  lemma_phi |= (.condition .geq (.var_label ⟨0, by omega⟩) (.var_label ⟨2, by omega⟩)) := by
    intros p Hp
    simp [lemma_phi] at *
    simp [Fin.foldr_succ] at Hp
    grind
