import PINN.Interval

/-! Pieces 384..389 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C064

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2474773, 2481778, 6279102514663241, 8292819479622593),
  (2481778, 2488721, 6279294835835921, 8261780807960495),
  (2488721, 2495716, 6242692196461442, 8258967337432182),
  (2495716, 2502680, 6225628494223929, 8227975421887963),
  (2502680, 2509666, 6189028972542101, 8208006021851351),
  (2509666, 2516621, 6163237551718871, 8168771283523968)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2474773, 2481778, 6279102514663241, 8292819479622593) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2481778, 2488721, 6279294835835921, 8261780807960495) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2488721, 2495716, 6242692196461442, 8258967337432182) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2495716, 2502680, 6225628494223929, 8227975421887963) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2502680, 2509666, 6189028972542101, 8208006021851351) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2509666, 2516621, 6163237551718871, 8168771283523968) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C064
