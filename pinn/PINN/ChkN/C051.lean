import PINN.Interval

/-! Pieces 306..311 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C051

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1657686, 1660245, -32830797459286, 86518874741387),
  (1660245, 1669845, -772463344113326, 848257411959836),
  (1669845, 1679573, -769335336116327, 879259894583201),
  (1679573, 1689301, -745020162466254, 888298094740378),
  (1689301, 1699097, -732403300757236, 908416318851328),
  (1699097, 1708955, -718854059581960, 927350592014004)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1657686, 1660245, -32830797459286, 86518874741387) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1660245, 1669845, -772463344113326, 848257411959836) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1669845, 1679573, -769335336116327, 879259894583201) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1679573, 1689301, -745020162466254, 888298094740378) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1689301, 1699097, -732403300757236, 908416318851328) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1699097, 1708955, -718854059581960, 927350592014004) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C051
