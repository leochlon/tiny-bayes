import PINN.Interval

/-! Pieces 318..323 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C053

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1767850, 1777962, -590451773768235, 1036094609148728),
  (1777962, 1788212, -586758277380272, 1071977351103097),
  (1788212, 1798448, -557621955385380, 1084567077532331),
  (1798448, 1808730, -537403259777778, 1108280678885687),
  (1808730, 1818994, -506250404888184, 1123471685461933),
  (1818994, 1829377, -495487195114290, 1161838131660624)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1767850, 1777962, -590451773768235, 1036094609148728) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1777962, 1788212, -586758277380272, 1071977351103097) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1788212, 1798448, -557621955385380, 1084567077532331) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1798448, 1808730, -537403259777778, 1108280678885687) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1808730, 1818994, -506250404888184, 1123471685461933) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1818994, 1829377, -495487195114290, 1161838131660624) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C053
