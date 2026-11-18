import FrameStep.L5
import FinalNorm

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem center_hidden_mem : List.Forall₂ (PRO.memAt PRO.S)
    (CON.lastHidden CON.pythia14m tokens) Output.center := by
  rw [center_hidden_eq]
  exact center_norm_sound Frame.L5.clast_mem

theorem saved_final_hidden_mem : List.Forall₂ (PRO.memAt PRO.S)
    (CON.lastHiddenFrom CON.pythia14m witnessInput) Output.witness := by
  rw [witness_hidden_eq]
  exact witness_norm_sound Frame.L5.wlast_mem

theorem actual_center_hidden_enclosed : List.Forall₂ Encloses
    (CON.lastHidden CON.pythia14m tokens) Output.center :=
  discharge_valid center_hidden_mem Output.center_valid

theorem actual_witness_hidden_enclosed : List.Forall₂ Encloses
    (CON.lastHiddenFrom CON.pythia14m witnessInput) Output.witness :=
  discharge_valid saved_final_hidden_mem Output.witness_valid

theorem actual_witness_gap : (1/20 : ℝ) ≤
    CON.logitFrom CON.pythia14m witnessInput 10895 -
      CON.logitFrom CON.pythia14m witnessInput 10166 :=
  Output.witness_gap_of_hidden saved_final_hidden_mem

#check actual_center_hidden_enclosed
#check actual_witness_hidden_enclosed
#check actual_witness_gap
#print axioms actual_center_hidden_enclosed
#print axioms actual_witness_hidden_enclosed
#print axioms actual_witness_gap
end PythiaCert
