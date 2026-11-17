import PINN.Interval

/-! Pieces 324..329 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C054

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1829377, 1835008, 107420480651470, 598921919611830),
  (1835008, 1845376, -444422504268612, 1192443943307675),
  (1845376, 1855744, -411162096797548, 1215874837510762),
  (1855744, 1866240, -396111027155001, 1261035341200260),
  (1866240, 1876768, -364151128995277, 1293082581572219),
  (1876768, 1887282, -323333819364464, 1319776481721240)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1829377, 1835008, 107420480651470, 598921919611830) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1835008, 1845376, -444422504268612, 1192443943307675) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1845376, 1855744, -411162096797548, 1215874837510762) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1855744, 1866240, -396111027155001, 1261035341200260) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1866240, 1876768, -364151128995277, 1293082581572219) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1876768, 1887282, -323333819364464, 1319776481721240) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C054
