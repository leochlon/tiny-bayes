import PINN.Interval

/-! Pieces 90..95 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C015

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (262144, 266368, -1591679756101356, 35109279238298),
  (266368, 270656, -2246070602464418, -600720700297092),
  (270656, 274944, -2865013942892728, -1242014613321938),
  (274944, 279296, -3486461928360391, -1847934703240801),
  (279296, 283712, -4093578333299514, -2441137545033329),
  (283712, 288128, -4660944935686606, -3035104137141521)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (262144, 266368, -1591679756101356, 35109279238298) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (266368, 270656, -2246070602464418, -600720700297092) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (270656, 274944, -2865013942892728, -1242014613321938) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (274944, 279296, -3486461928360391, -1847934703240801) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (279296, 283712, -4093578333299514, -2441137545033329) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (283712, 288128, -4660944935686606, -3035104137141521) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C015
