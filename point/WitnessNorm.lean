import WitnessLayer0
import FixedPrefix
import FiniteLinear

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def witnessVector : Fin 128 → ℝ := fun i => witnessDelta.getD i.val 0

theorem witnessDelta_length : witnessDelta.length = 128 := by
  simp only [witnessDelta, List.length_map, WitnessDomain.coordinate_count]

theorem witnessVector_bound (i : Fin 128) : |witnessVector i| ≤ (37/16384 : ℝ) := by
  apply witness_delta_bound
  unfold witnessVector
  rw [List.getD_eq_getElem _ _ (by rw [witnessDelta_length]; exact i.isLt)]
  exact List.getElem_mem _

/-- The norm here is the supremum norm on all128 saved coordinates. -/
theorem witnessVector_norm : ‖witnessVector‖ = (37/16384 : ℝ) := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 37/16384)]
    intro i
    simpa only [Real.norm_eq_abs] using witnessVector_bound i
  · have h := norm_le_pi_norm witnessVector (⟨2, by decide⟩ : Fin 128)
    change |witnessDelta.getD 2 0| ≤ ‖witnessVector‖ at h
    rw [witness_delta_attains] at h
    exact h

theorem witnessVector_ofFn : List.ofFn witnessVector = witnessDelta :=
  FiniteLinear.ofFn_rowFn witnessDelta witnessDelta_length

/-- Exact input used by the witness logit theorem, with the coordinate-domain
perturbation made explicit. No token or coordinate is removed. -/
theorem witnessInput_eq_vector : witnessInput =
    fixedPrefixInput ++ [CON.vadd input31 (List.ofFn witnessVector)] := by
  rw [witnessVector_ofFn]
  rfl

#check witnessVector_norm
#check witnessInput_eq_vector
#print axioms witnessVector_bound
#print axioms witnessVector_norm
#print axioms witnessInput_eq_vector
end PythiaCert
