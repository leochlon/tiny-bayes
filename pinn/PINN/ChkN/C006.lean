import PINN.Interval

/-! Pieces 36..41 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C006

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (56064, 58418, -252323105004105, 1397690097533900),
  (58418, 60850, 1070921864435164, 2720654043792605),
  (60850, 63363, 2371243652896693, 4019616990599888),
  (63363, 65966, 3645675594427821, 5294721500637606),
  (65966, 68643, 4896423121331496, 6529538051654482),
  (68643, 71424, 6104129230635609, 7739772075592302)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (56064, 58418, -252323105004105, 1397690097533900) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (58418, 60850, 1070921864435164, 2720654043792605) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (60850, 63363, 2371243652896693, 4019616990599888) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (63363, 65966, 3645675594427821, 5294721500637606) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (65966, 68643, 4896423121331496, 6529538051654482) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (68643, 71424, 6104129230635609, 7739772075592302) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C006
