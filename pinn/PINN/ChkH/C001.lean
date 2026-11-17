import PINN.Interval

/-! Pieces 6..11 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C001

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (29906, 35238, 91443638338765, 2108941863997830),
  (35238, 40635, 681697812588868, 2682497476919991),
  (40635, 46158, 1204824137879905, 3228159623686573),
  (46158, 51713, 1708376361822703, 3695256200458967),
  (51713, 57355, 2144012457245644, 4130346674010081),
  (57355, 63102, 2526550136592715, 4525371937071377)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (29906, 35238, 91443638338765, 2108941863997830) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (35238, 40635, 681697812588868, 2682497476919991) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (40635, 46158, 1204824137879905, 3228159623686573) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (46158, 51713, 1708376361822703, 3695256200458967) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (51713, 57355, 2144012457245644, 4130346674010081) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (57355, 63102, 2526550136592715, 4525371937071377) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C001
