import PINN.Interval

/-! Pieces 72..77 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C012

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (191530, 195626, 10612940923280655, 12245243683732607),
  (195626, 199722, 9908018737787325, 11553560798591620),
  (199722, 203806, 9196525800111697, 10844859773067403),
  (203806, 207851, 8489253355098951, 10120988117900682),
  (207851, 211881, 7773331240710851, 9400248770739785),
  (211881, 215955, 7032333554278907, 8689707969406571)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (191530, 195626, 10612940923280655, 12245243683732607) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (195626, 199722, 9908018737787325, 11553560798591620) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (199722, 203806, 9196525800111697, 10844859773067403) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (203806, 207851, 8489253355098951, 10120988117900682) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (207851, 211881, 7773331240710851, 9400248770739785) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (211881, 215955, 7032333554278907, 8689707969406571) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C012
