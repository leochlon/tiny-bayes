import PINN.Interval

/-! Pieces 30..35 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C005

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (43330, 45309, -8570995668299037, -6914028334600805),
  (45309, 47342, -7144639646320964, -5488606221070833),
  (47342, 49433, -5732056127040931, -4076114800355460),
  (49433, 51582, -4333364902432699, -2680511147664897),
  (51582, 53802, -2952860459664034, -1295717806739800),
  (53802, 56064, -1582443612936141, 51576780550694)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (43330, 45309, -8570995668299037, -6914028334600805) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (45309, 47342, -7144639646320964, -5488606221070833) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (47342, 49433, -5732056127040931, -4076114800355460) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (49433, 51582, -4333364902432699, -2680511147664897) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (51582, 53802, -2952860459664034, -1295717806739800) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (53802, 56064, -1582443612936141, 51576780550694) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C005
