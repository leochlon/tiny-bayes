import PINN.Interval

/-! Pieces 420..425 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C070

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2715605, 2722389, 3478488313084158, 5484479560155089),
  (2722389, 2729173, 3342393814380620, 5350212859386134),
  (2729173, 2735957, 3204222576615974, 5213774072140265),
  (2735957, 2742722, 3069570969349643, 5070186260939423),
  (2742722, 2749511, 2920860193841302, 4936684039594157),
  (2749511, 2756259, 2789273025681527, 4782749798004657)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2715605, 2722389, 3478488313084158, 5484479560155089) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2722389, 2729173, 3342393814380620, 5350212859386134) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2729173, 2735957, 3204222576615974, 5213774072140265) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2735957, 2742722, 3069570969349643, 5070186260939423) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2742722, 2749511, 2920860193841302, 4936684039594157) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2749511, 2756259, 2789273025681527, 4782749798004657) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C070
