import PINN.Interval

/-! Pieces 270..275 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C045

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1351629, 1359888, -2177935477119712, -538563047987199),
  (1359888, 1368172, -2115443331553965, -478979349624661),
  (1368172, 1376473, -2051880341573639, -421250269993712),
  (1376473, 1384836, -1997220288308753, -355437177933779),
  (1384836, 1393230, -1936849607267343, -296367552524511),
  (1393230, 1398101, -1351646052694084, -788428223201243)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1351629, 1359888, -2177935477119712, -538563047987199) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1359888, 1368172, -2115443331553965, -478979349624661) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1368172, 1376473, -2051880341573639, -421250269993712) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1376473, 1384836, -1997220288308753, -355437177933779) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1384836, 1393230, -1936849607267343, -296367552524511) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1393230, 1398101, -1351646052694084, -788428223201243) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C045
