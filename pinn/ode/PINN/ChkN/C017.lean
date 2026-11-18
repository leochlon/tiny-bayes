import PINN.Interval

/-! Pieces 102..107 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C017

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (315915, 320707, -8133818153211705, -6503069299283836),
  (320707, 325603, -8541413897213418, -6884668225977990),
  (325603, 330555, -8906889650202667, -7254076654543733),
  (330555, 335520, -9227760317984512, -7604770075097874),
  (335520, 340607, -9550399763337736, -7893293144803523),
  (340607, 345762, -9827085415210019, -8167896296758674)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (315915, 320707, -8133818153211705, -6503069299283836) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (320707, 325603, -8541413897213418, -6884668225977990) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (325603, 330555, -8906889650202667, -7254076654543733) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (330555, 335520, -9227760317984512, -7604770075097874) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (335520, 340607, -9550399763337736, -7893293144803523) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (340607, 345762, -9827085415210019, -8167896296758674) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C017
