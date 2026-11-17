import PINN.Interval

/-! Pieces 438..443 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C073

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3145728, 3160832, -4383411790263442, -2728469064770557),
  (3160832, 3175936, -4563800344774383, -2928951207757356),
  (3175936, 3191123, -4747490850328976, -3116295001056198),
  (3191123, 3206540, -4941408810169218, -3285170265101181),
  (3206540, 3221900, -5100219669491221, -3477918032231363),
  (3221900, 3233109, -4878309939540729, -3991773510050715)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3145728, 3160832, -4383411790263442, -2728469064770557) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3160832, 3175936, -4563800344774383, -2928951207757356) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3175936, 3191123, -4747490850328976, -3116295001056198) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3191123, 3206540, -4941408810169218, -3285170265101181) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3206540, 3221900, -5100219669491221, -3477918032231363) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3221900, 3233109, -4878309939540729, -3991773510050715) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C073
