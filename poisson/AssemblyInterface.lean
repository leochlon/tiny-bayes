import Correction
import Point
namespace PoissonR3
open Set PoissonPilot

/-- Only the global residual obligation remains; both other numerical premises are closed. -/
theorem bracket_with_residual
    (hres : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 →
      |-Lap (fun a b => N a b-C a b) x y-forcing x y| ≤ certR)
    (u : ℝ → ℝ → ℝ)
    (hcu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Q) (hdu : CoordTwoOn u)
    (hbu : ∀ z ∈ Q, Edge z → u z.1 z.2=0)
    (hpu : ∀ x y, x ∈ Ioo (0:ℝ) 1 → y ∈ Ioo (0:ℝ) 1 → -Lap u x y=forcing x y) :
    (∀ z ∈ Q, |N z.1 z.2-u z.1 z.2| ≤ certU) ∧
      certL ≤ |N witness.1 witness.2-u witness.1 witness.2| :=
  frozen_bracket_conditional hC hres hpoint u hcu hdu hbu hpu

#check hC
#check hpoint
#check bracket_with_residual
#print axioms hC
#print axioms hpoint
#print axioms bracket_with_residual
end PoissonR3
