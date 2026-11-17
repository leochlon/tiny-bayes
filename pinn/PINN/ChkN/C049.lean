import PINN.Interval

/-! Pieces 294..299 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C049

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1548285, 1557406, -1058817711220538, 577971760561673),
  (1557406, 1566584, -1030646343812099, 611056397604818),
  (1566584, 1572864, -569600696828671, 199058818551522),
  (1572864, 1582080, -976667560005997, 652919598196234),
  (1582080, 1591424, -964977778054693, 694291322175967),
  (1591424, 1600768, -932087430140312, 711724693067881)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1548285, 1557406, -1058817711220538, 577971760561673) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1557406, 1566584, -1030646343812099, 611056397604818) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1566584, 1572864, -569600696828671, 199058818551522) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1572864, 1582080, -976667560005997, 652919598196234) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1582080, 1591424, -964977778054693, 694291322175967) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1591424, 1600768, -932087430140312, 711724693067881) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C049
