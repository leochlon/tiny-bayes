import PINN.Interval

/-! Pieces 396..401 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C066

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2612438, 2621440, 2409163010920145, 3195514913125623),
  (2621440, 2634624, 1916395270347328, 3563550866984345),
  (2634624, 2647808, 1839642090577158, 3480200566088322),
  (2647808, 2661035, 1751112871299618, 3395580726951679),
  (2661035, 2674288, 1658176708602044, 3302217198101904),
  (2674288, 2687507, 1566222998695162, 3195411587017831)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2612438, 2621440, 2409163010920145, 3195514913125623) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2621440, 2634624, 1916395270347328, 3563550866984345) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2634624, 2647808, 1839642090577158, 3480200566088322) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2647808, 2661035, 1751112871299618, 3395580726951679) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2661035, 2674288, 1658176708602044, 3302217198101904) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2674288, 2687507, 1566222998695162, 3195411587017831) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C066
