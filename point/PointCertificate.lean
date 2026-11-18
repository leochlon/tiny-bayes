import FinalPoint
import AllOutput
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem actual_center_margin : ∀ j : Fin 50304, j.val ≠ 10166 →
    (2 : ℝ) ≤ CON.logit CON.pythia14m tokens 10166 - CON.logit CON.pythia14m tokens j.val :=
  Output.all_center_rows_of_blocks center_hidden_mem Output.all_blocks_checked
#check actual_center_margin
#print axioms actual_center_margin
#check actual_witness_gap
#print axioms actual_witness_gap
end PythiaCert
