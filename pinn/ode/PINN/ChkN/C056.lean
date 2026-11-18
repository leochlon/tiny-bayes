import PINN.Interval

/-! Pieces 336..341 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C056

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1943637, 1954389, -72620193030616, 1583261602919316),
  (1954389, 1965097, -13271580901137, 1619885644891442),
  (1965097, 1975917, 24554950793109, 1681997328576643),
  (1975917, 1986760, 77892361670594, 1732830074601860),
  (1986760, 1997635, 131885488437493, 1786805560064679),
  (1997635, 2008537, 188599714171367, 1841772514104860)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1943637, 1954389, -72620193030616, 1583261602919316) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1954389, 1965097, -13271580901137, 1619885644891442) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1965097, 1975917, 24554950793109, 1681997328576643) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1975917, 1986760, 77892361670594, 1732830074601860) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1986760, 1997635, 131885488437493, 1786805560064679) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1997635, 2008537, 188599714171367, 1841772514104860) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C056
