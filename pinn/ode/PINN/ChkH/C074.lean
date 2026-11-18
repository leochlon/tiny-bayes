import PINN.Interval

/-! Pieces 444..449 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C074

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2877601, 2883584, 101243635944140, 1685272846569193),
  (2883584, 2890368, -260766936287665, 1753042434351750),
  (2890368, 2897152, -415830529129862, 1596517986180983),
  (2897152, 2903936, -570142324575543, 1440597225988350),
  (2903936, 2910720, -723577522625501, 1285414961263164),
  (2910720, 2917485, -870559901126027, 1126084229297018)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2877601, 2883584, 101243635944140, 1685272846569193) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2883584, 2890368, -260766936287665, 1753042434351750) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2890368, 2897152, -415830529129862, 1596517986180983) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2897152, 2903936, -570142324575543, 1440597225988350) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2903936, 2910720, -723577522625501, 1285414961263164) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2910720, 2917485, -870559901126027, 1126084229297018) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C074
