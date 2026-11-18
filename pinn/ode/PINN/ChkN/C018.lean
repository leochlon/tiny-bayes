import PINN.Interval

/-! Pieces 108..113 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C018

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (345762, 349525, -9664294399928814, -8752677794010942),
  (349525, 354773, -10218036355608940, -8571244184095539),
  (354773, 360085, -10401268923021983, -8756179923957539),
  (360085, 365461, -10549882774312961, -8906871961166494),
  (365461, 370901, -10663513183893148, -9022840266772148),
  (370901, 376405, -10741938605619977, -9103740533279803)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (345762, 349525, -9664294399928814, -8752677794010942) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (349525, 354773, -10218036355608940, -8571244184095539) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (354773, 360085, -10401268923021983, -8756179923957539) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (360085, 365461, -10549882774312961, -8906871961166494) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (365461, 370901, -10663513183893148, -9022840266772148) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (370901, 376405, -10741938605619977, -9103740533279803) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C018
