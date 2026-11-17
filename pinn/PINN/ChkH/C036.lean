import PINN.Interval

/-! Pieces 216..221 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C036

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1344335, 1351056, 213879002152660, 2211238647186847),
  (1351056, 1357763, 64508142994657, 2052556467498292),
  (1357763, 1364538, -108046674108696, 1917467085960128),
  (1364538, 1371289, -253711091212254, 1756429609931629),
  (1371289, 1377992, -390600095286996, 1590437003661947),
  (1377992, 1384747, -554783528525117, 1454109119504909)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1344335, 1351056, 213879002152660, 2211238647186847) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1351056, 1357763, 64508142994657, 2052556467498292) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1357763, 1364538, -108046674108696, 1917467085960128) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1364538, 1371289, -253711091212254, 1756429609931629) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1371289, 1377992, -390600095286996, 1590437003661947) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1377992, 1384747, -554783528525117, 1454109119504909) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C036
