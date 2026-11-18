import Mathlib

/-! The exact GELU activation over `ℝ`. -/

namespace PRO

noncomputable section

/-- Standard normal distribution function `Φ x = 1/2 + (2π)^(-1/2) ∫_0^x exp (-t²/2) dt`
(equal to `(1 + erf (x / √2)) / 2`). -/
def Phi (x : ℝ) : ℝ :=
  1 / 2 + intervalIntegral (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) 0 x MeasureTheory.volume /
    Real.sqrt (2 * Real.pi)

/-- Exact GELU. -/
def gelu (x : ℝ) : ℝ := x * Phi x

end

end PRO
