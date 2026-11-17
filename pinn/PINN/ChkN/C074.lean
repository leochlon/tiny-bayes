import PINN.Interval

/-! Pieces 444..449 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C074

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3233109, 3248853, -5406649315081550, -3747991605082430),
  (3248853, 3264725, -5565830897267619, -3906736798628013),
  (3264725, 3280626, -5706428938319351, -4067350988424063),
  (3280626, 3296664, -5848126721474158, -4208883790769084),
  (3296664, 3312857, -5981877683104584, -4339938937414023),
  (3312857, 3320490, -5446775289754613, -5056598009698695)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3233109, 3248853, -5406649315081550, -3747991605082430) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3248853, 3264725, -5565830897267619, -3906736798628013) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3264725, 3280626, -5706428938319351, -4067350988424063) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3280626, 3296664, -5848126721474158, -4208883790769084) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3296664, 3312857, -5981877683104584, -4339938937414023) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3312857, 3320490, -5446775289754613, -5056598009698695) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C074
