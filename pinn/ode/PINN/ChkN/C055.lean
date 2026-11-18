import PINN.Interval

/-! Pieces 330..335 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C055

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1887282, 1897841, -289956574111338, 1357544348278672),
  (1897841, 1908388, -245883149335343, 1388338132032030),
  (1908388, 1918998, -211367844326577, 1432538107668507),
  (1918998, 1922389, 549492092485864, 725790011595757),
  (1922389, 1933013, -152354310911416, 1483427983418280),
  (1933013, 1943637, -103876259082245, 1522610239479841)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1887282, 1897841, -289956574111338, 1357544348278672) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1897841, 1908388, -245883149335343, 1388338132032030) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1908388, 1918998, -211367844326577, 1432538107668507) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1918998, 1922389, 549492092485864, 725790011595757) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1922389, 1933013, -152354310911416, 1483427983418280) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1933013, 1943637, -103876259082245, 1522610239479841) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C055
