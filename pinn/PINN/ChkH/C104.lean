import PINN.Interval

/-! Pieces 624..629 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C104

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4049541, 4055425, 1345186898998476, 3347758041359928),
  (4055425, 4061309, 814435349547904, 2838614133036753),
  (4061309, 4067100, 294206756476748, 2284926276316164),
  (4067100, 4072855, -258003141143810, 1732825441810087),
  (4072855, 4078577, -828821464326572, 1163567635129769),
  (4078577, 4084279, -1422322603104938, 579823507792165)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4049541, 4055425, 1345186898998476, 3347758041359928) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4055425, 4061309, 814435349547904, 2838614133036753) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4061309, 4067100, 294206756476748, 2284926276316164) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4067100, 4072855, -258003141143810, 1732825441810087) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4072855, 4078577, -828821464326572, 1163567635129769) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4078577, 4084279, -1422322603104938, 579823507792165) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C104
