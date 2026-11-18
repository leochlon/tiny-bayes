import PINN.Interval

/-! Pieces 90..95 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C015

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (524288, 530752, -4492235059610420, -2474576103667726),
  (530752, 537216, -4370479774639648, -2348081846040665),
  (537216, 543680, -4241563088012010, -2214737109282353),
  (543680, 550080, -4087174542384224, -2094894560075390),
  (550080, 556515, -3956679670085003, -1939226103977619),
  (556515, 562925, -3801527209296893, -1796016661763746)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (524288, 530752, -4492235059610420, -2474576103667726) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (530752, 537216, -4370479774639648, -2348081846040665) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (537216, 543680, -4241563088012010, -2214737109282353) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (543680, 550080, -4087174542384224, -2094894560075390) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (550080, 556515, -3956679670085003, -1939226103977619) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (556515, 562925, -3801527209296893, -1796016661763746) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C015
