import PINN.Interval

/-! Pieces 222..227 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C037

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1384747, 1391528, -711011065915324, 1310819277332553),
  (1391528, 1398101, -797459847478674, 1104724618320599),
  (1398101, 1404885, -1000607558223621, 1018404379970847),
  (1404885, 1411669, -1144702739903641, 871982564513329),
  (1411669, 1418453, -1286906277888799, 727434601273754),
  (1418453, 1425237, -1427068151013863, 584852987498551)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1384747, 1391528, -711011065915324, 1310819277332553) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1391528, 1398101, -797459847478674, 1104724618320599) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1398101, 1404885, -1000607558223621, 1018404379970847) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1404885, 1411669, -1144702739903641, 871982564513329) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1411669, 1418453, -1286906277888799, 727434601273754) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1418453, 1425237, -1427068151013863, 584852987498551) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C037
