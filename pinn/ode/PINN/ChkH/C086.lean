import PINN.Interval

/-! Pieces 516..521 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C086

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3361332, 3368058, -3618981664726483, -1631500413115512),
  (3368058, 3374823, -3512350527477880, -1495713028136807),
  (3374823, 3381536, -3374435363610431, -1381387408181454),
  (3381536, 3388222, -3239323790705771, -1255899606154421),
  (3388222, 3394900, -3105304792982836, -1120410691532210),
  (3394900, 3401588, -2971656457942224, -975051379482403)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3361332, 3368058, -3618981664726483, -1631500413115512) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3368058, 3374823, -3512350527477880, -1495713028136807) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3374823, 3381536, -3374435363610431, -1381387408181454) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3381536, 3388222, -3239323790705771, -1255899606154421) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3388222, 3394900, -3105304792982836, -1120410691532210) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3394900, 3401588, -2971656457942224, -975051379482403) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C086
