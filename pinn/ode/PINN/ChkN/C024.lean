import PINN.Interval

/-! Pieces 144..149 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C024

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (529472, 534656, -3305868800637175, -1680734936733147),
  (534656, 539904, -2961249771731966, -1309349184645266),
  (539904, 545152, -2600167874654338, -958303523118132),
  (545152, 550400, -2243607885477433, -612573198713365),
  (550400, 555665, -1896643556097344, -267502830607695),
  (555665, 560970, -1559950004927860, 78836862185794)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (529472, 534656, -3305868800637175, -1680734936733147) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (534656, 539904, -2961249771731966, -1309349184645266) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (539904, 545152, -2600167874654338, -958303523118132) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (545152, 550400, -2243607885477433, -612573198713365) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (550400, 555665, -1896643556097344, -267502830607695) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (555665, 560970, -1559950004927860, 78836862185794) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C024
