import AssemblyInterface
import FullResidual
namespace PoissonR3
open Set PoissonPilot

-- This module is deliberately pending until all actual numerical shards close FullResidual.
theorem frozen_bracket
    (u : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q) (hdu : CoordTwoOn u)
    (hbu : ∀ z ∈ Q, Edge z → u z.1 z.2=0)
    (hpu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=forcing x y) :
    (∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ certU) ∧
      certL ≤ |N witness.1 witness.2-u witness.1 witness.2| :=
  bracket_with_residual PinnCertFarm.hres u hcu hdu hbu hpu

theorem frozen_reference_bracket :
    (∀ z ∈ Q, |N z.1 z.2-U z.1 z.2| ≤ certU) ∧
      certL ≤ |N witness.1 witness.2-U witness.1 witness.2| :=
  frozen_bracket U reference_is_solution.1 reference_is_solution.2.1
    reference_is_solution.2.2.1 reference_is_solution.2.2.2

theorem frozen_reference_accuracy :
    (∀ z ∈ Q, |N z.1 z.2-U z.1 z.2| < (1:ℝ)/30000) ∧
      (1:ℝ)/80000 ≤ |N witness.1 witness.2-U witness.1 witness.2| := by
  constructor
  · intro z hz
    exact lt_of_le_of_lt (frozen_reference_bracket.1 z hz) candidate_arithmetic.1
  · exact le_trans candidate_arithmetic.2.1 frozen_reference_bracket.2

#check frozen_bracket
#check frozen_reference_bracket
#check frozen_reference_accuracy
#print axioms frozen_bracket
#print axioms frozen_reference_bracket
#print axioms frozen_reference_accuracy
end PoissonR3
