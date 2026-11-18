import Layer0Prefix

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def fixedPrefixInput : List (List ℝ) := input.take 31
def fixedPrefixQ : List (List PRO.Iv) := layer0_q.take 31

theorem fixedPrefixInput_length : fixedPrefixInput.length = 31 := by
  simp [fixedPrefixInput, input_length]
theorem fixedPrefixQ_length : fixedPrefixQ.length = 31 := by decide +kernel

/-- The actual frozen first31 QKV rows, with validity discharged. -/
theorem actual_fixed_prefix_qkv : List.Forall₂ (List.Forall₂ Encloses)
    (fixedPrefixInput.map fun x => CON.qkv CON.layer0
      (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b x)) fixedPrefixQ := by
  have h := List.forall₂_take 31 actual_all32_layer0_qkv_enclosed
  simpa only [fixedPrefixInput, fixedPrefixQ, input, CON.take_map_eq] using h

/-- Arbitrarily replacing the final embedding does not change these QKV rows. -/
theorem actual_perturbed_prefix_qkv (z : List ℝ) : List.Forall₂ (List.Forall₂ Encloses)
    (((fixedPrefixInput ++ [z]).take 31).map fun x => CON.qkv CON.layer0
      (CON.layerNorm CON.layer0.ln1g CON.layer0.ln1b x)) fixedPrefixQ := by
  have he : (fixedPrefixInput ++ [z]).take 31 = fixedPrefixInput := by
    rw [List.take_append_of_le_length (by rw [fixedPrefixInput_length])]
    exact List.take_of_length_le (by rw [fixedPrefixInput_length])
  rw [he]
  exact actual_fixed_prefix_qkv

#check actual_fixed_prefix_qkv
#check actual_perturbed_prefix_qkv
#print axioms actual_fixed_prefix_qkv
#print axioms actual_perturbed_prefix_qkv
end PythiaCert
