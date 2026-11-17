import PINN.Interval

/-! Pieces 312..317 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C052

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1708955, 1718774, -688793526501823, 929623277027287),
  (1718774, 1728691, -681137970307592, 954479772409888),
  (1728691, 1738602, -656183308018171, 962543208292681),
  (1738602, 1747626, -496517180992838, 834984026035323),
  (1747626, 1757738, -641845221990514, 1013562609827792),
  (1757738, 1767850, -616150711224304, 1024130454519385)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1708955, 1718774, -688793526501823, 929623277027287) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1718774, 1728691, -681137970307592, 954479772409888) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1728691, 1738602, -656183308018171, 962543208292681) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1738602, 1747626, -496517180992838, 834984026035323) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1747626, 1757738, -641845221990514, 1013562609827792) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1757738, 1767850, -616150711224304, 1024130454519385) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C052
