import PINN.Interval

/-! Pieces 348..353 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C058

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2064601, 2075662, 571611800721602, 2211478180646118),
  (2075662, 2086742, 640509772736950, 2275572978747861),
  (2086742, 2097152, 804293547184536, 2242573734519108),
  (2097152, 2108288, 774126518499308, 2405290158407288),
  (2108288, 2119552, 830577428911860, 2487865600400258),
  (2119552, 2130847, 902011348614405, 2557380554706859)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2064601, 2075662, 571611800721602, 2211478180646118) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2075662, 2086742, 640509772736950, 2275572978747861) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2086742, 2097152, 804293547184536, 2242573734519108) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2097152, 2108288, 774126518499308, 2405290158407288) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2108288, 2119552, 830577428911860, 2487865600400258) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2119552, 2130847, 902011348614405, 2557380554706859) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C058
