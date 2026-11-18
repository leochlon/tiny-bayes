import PINN.Interval

/-! Pieces 150..155 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C025

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (560970, 566317, -1227872655924060, 420744982917222),
  (566317, 571675, -892813786137847, 747323549349375),
  (571675, 577065, -570559386872148, 1072203547441125),
  (577065, 582472, -251672968637433, 1384983652529245),
  (582472, 587947, 46476015826376, 1703870107388284),
  (587947, 593414, 357096995190031, 1992816399117377)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (560970, 566317, -1227872655924060, 420744982917222) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (566317, 571675, -892813786137847, 747323549349375) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (571675, 577065, -570559386872148, 1072203547441125) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (577065, 582472, -251672968637433, 1384983652529245) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (582472, 587947, 46476015826376, 1703870107388284) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (587947, 593414, 357096995190031, 1992816399117377) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C025
