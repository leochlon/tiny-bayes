import PINN.Interval

/-! Pieces 120..125 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C020

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (711850, 718250, 794053659082455, 2786280162956340),
  (718250, 724714, 974869304467326, 3001445766247776),
  (724714, 731162, 1178612511223639, 3191739515525132),
  (731162, 737639, 1367164778575234, 3393689310509831),
  (737639, 744120, 1561737395239699, 3586271732762157),
  (744120, 750565, 1765394391141143, 3764016785770750)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (711850, 718250, 794053659082455, 2786280162956340) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (718250, 724714, 974869304467326, 3001445766247776) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (724714, 731162, 1178612511223639, 3191739515525132) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (731162, 737639, 1367164778575234, 3393689310509831) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (737639, 744120, 1561737395239699, 3586271732762157) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (744120, 750565, 1765394391141143, 3764016785770750) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C020
