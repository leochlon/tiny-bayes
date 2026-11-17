import PINN.Interval

/-! Pieces 246..251 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C041

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1547168, 1554093, -3598829639434928, -1569969323122564),
  (1554093, 1560985, -3668902510876071, -1663421553755733),
  (1560985, 1567852, -3737241439202054, -1749935122839615),
  (1567852, 1572864, -3342612141442586, -2271788093465305),
  (1572864, 1579776, -3870579991384722, -1865415578121264),
  (1579776, 1586688, -3934987362906344, -1934230808580329)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1547168, 1554093, -3598829639434928, -1569969323122564) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1554093, 1560985, -3668902510876071, -1663421553755733) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1560985, 1567852, -3737241439202054, -1749935122839615) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1567852, 1572864, -3342612141442586, -2271788093465305) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1572864, 1579776, -3870579991384722, -1865415578121264) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1579776, 1586688, -3934987362906344, -1934230808580329) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C041
