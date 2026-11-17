import PINN.Interval

/-! Pieces 480..485 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C080

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3791189, 3807936, -2571871814398206, -934041828743193),
  (3807936, 3824629, -2150125642713172, -510230867174452),
  (3824629, 3841314, -1711201526277800, -61278299109669),
  (3841314, 3844778, -681822115269333, -533409467160698),
  (3844778, 3861418, -1149671302014585, 506361713183627),
  (3861418, 3877802, -646727105750225, 977452206911729)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3791189, 3807936, -2571871814398206, -934041828743193) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3807936, 3824629, -2150125642713172, -510230867174452) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3824629, 3841314, -1711201526277800, -61278299109669) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3841314, 3844778, -681822115269333, -533409467160698) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3844778, 3861418, -1149671302014585, 506361713183627) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3861418, 3877802, -646727105750225, 977452206911729) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C080
