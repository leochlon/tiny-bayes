import PerturbationModel

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem input_eq_prefix_last : input = fixedPrefixInput ++ [input31] := rfl

theorem vadd_replicate_zero (xs : List ℝ) :
    CON.vadd xs (List.replicate xs.length 0) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (a + 0) :: CON.vadd xs (List.replicate xs.length 0) = a :: xs
    rw [add_zero, ih]

/-- The zero perturbation is exactly the frozen32-token embedding input. -/
theorem perturbInput_zero : perturbInput (0 : Fin 128 → ℝ) = input := by
  rw [input_eq_prefix_last]
  unfold perturbInput
  congr 2
  have hzero : List.ofFn (0 : Fin 128 → ℝ) = List.replicate 128 0 := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [hzero, ← input31_length, vadd_replicate_zero]

/-- The closed ball quantifies independently over all128 coordinates. -/
theorem closed_ball_iff_coordinates (δ : Fin 128 → ℝ) :
    ‖δ‖ ≤ (1/65536 : ℝ) ↔ ∀ i, |δ i| ≤ (1/65536 : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/65536)]
  simp only [Real.norm_eq_abs]

theorem zero_perturbation_logits (j : Fin 50304) :
    CON.logitFrom CON.pythia14m (perturbInput (0 : Fin 128 → ℝ)) j.val =
      CON.logit CON.pythia14m tokens j.val := by
  rw [perturbInput_zero]
  exact CON.logitFrom_tokens _ _ _

theorem saved_witness_domain :
    ‖witnessVector‖ = (37/16384 : ℝ) ∧
      perturbInput witnessVector = witnessInput :=
  ⟨witnessVector_norm, witnessInput_eq_perturbInput.symm⟩

#check perturbInput_zero
#check closed_ball_iff_coordinates
#check zero_perturbation_logits
#check saved_witness_domain
#print axioms perturbInput_zero
#print axioms closed_ball_iff_coordinates
#print axioms zero_perturbation_logits
#print axioms saved_witness_domain
end PythiaCert
