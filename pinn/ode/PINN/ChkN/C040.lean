import PINN.Interval

/-! Pieces 240..245 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C040

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1121878, 1129357, -3148856312260312, -1532845110915341),
  (1129357, 1135957, -2985932021386605, -1737418722952815),
  (1135957, 1143573, -3199375451661245, -1555704298370946),
  (1143573, 1151253, -3216247803168403, -1561784286103608),
  (1151253, 1158933, -3213845602802865, -1575996600188832),
  (1158933, 1166669, -3220893909293182, -1569946497750634)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1121878, 1129357, -3148856312260312, -1532845110915341) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1129357, 1135957, -2985932021386605, -1737418722952815) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1135957, 1143573, -3199375451661245, -1555704298370946) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1143573, 1151253, -3216247803168403, -1561784286103608) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1151253, 1158933, -3213845602802865, -1575996600188832) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1158933, 1166669, -3220893909293182, -1569946497750634) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C040
