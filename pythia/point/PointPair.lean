import PointCertificate
import PerturbationDomain

namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The exact frozen full-vocabulary center and saved-witness target.
This module can only compile after the actual six-layer point chain closes. -/
theorem actual_frozen_point_pair :
    (∀ j : Fin 50304, j.val ≠ 10166 →
      (2 : ℝ) ≤ CON.logit CON.pythia14m tokens 10166 -
        CON.logit CON.pythia14m tokens j.val) ∧
    ‖witnessVector‖ = (37/16384 : ℝ) ∧
    (1/20 : ℝ) ≤
      CON.logitFrom CON.pythia14m (perturbInput witnessVector) 10895 -
        CON.logitFrom CON.pythia14m (perturbInput witnessVector) 10166 := by
  refine ⟨actual_center_margin, witnessVector_norm, ?_⟩
  rw [← witnessInput_eq_perturbInput]
  exact actual_witness_gap

#check actual_frozen_point_pair
#print axioms actual_frozen_point_pair
end PythiaCert
