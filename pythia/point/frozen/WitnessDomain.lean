import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace WitnessDomain

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def numerators : List Int := [-3789, -34156, 37888, -37888, -15488, 37888, -37888, -37888, 37888, 14542, 37888, 37888, 37888, 37888, 37888, 37888, 20838, 37888, 37888, 37888, -37888, -37888, 37888, 37888, -34835, 37888, 37888, 37888, -34531, 1894, -37888, 37888, -33750, -18023, -13433, -13894, -37888, 37888, 1894, -37888, -34618, -21100, 37888, 37888, -37888, 37888, -37888, 7860, 26897, 37888, 37888, -37888, -37888, -32358, -37888, -22069, 37888, 32277, 28456, 4229, 25583, 37888, 37888, -37888, -37888, -11868, -37888, -37888, 37888, 37888, -37888, 37888, 37888, -37888, -37888, -37888, -37888, 37888, -24475, 37888, 35516, -37888, -20838, -1894, 37888, -37888, 29505, 37888, -13372, 37888, -22792, 37888, -37888, 37888, -36265, -37888, 37888, -29958, -15155, -27231, 16733, 37888, 37888, -37888, 30549, -37888, 37888, 37888, -37888, 37888, -37888, 23697, -21252, 29295, -34290, 37888, -20608, 21188, -1894, -37888, 37888, -37888, 11945, 20838, -37888, -29097, -37888, 37888]

theorem coordinate_count : numerators.length = 128 := by decide

theorem integer_envelope : ∀ z ∈ numerators, (-37888 : Int) ≤ z ∧ z ≤ 37888 := by decide

theorem endpoint_present : (37888 : Int) ∈ numerators := by decide

theorem scaled_envelope (z : Int) (hz : z ∈ numerators) :
    -(37 / 16384 : ℝ) ≤ (z : ℝ) / 16777216 ∧
    (z : ℝ) / 16777216 ≤ (37 / 16384 : ℝ) := by
  have h := integer_envelope z hz
  have hl : (-37888 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h.1
  have hu : (z : ℝ) ≤ (37888 : ℝ) := by exact_mod_cast h.2
  constructor <;> linarith

theorem endpoint_scaled : (37888 : ℝ) / 16777216 = (1 * 37 / 16384 : ℝ) := by norm_num

#check coordinate_count
#print axioms coordinate_count
#check integer_envelope
#print axioms integer_envelope
#check endpoint_present
#print axioms endpoint_present
#check scaled_envelope
#print axioms scaled_envelope
#check endpoint_scaled
#print axioms endpoint_scaled
end WitnessDomain
