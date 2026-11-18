import PINN.Interval

/-! Pieces 618..623 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C103

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4014629, 4019541, 4361037934056810, 5725021795681698),
  (4019541, 4025621, 3664749367009655, 5677514881815607),
  (4025621, 4031637, 3244566469731408, 5240427408136667),
  (4031637, 4037653, 2787131156830983, 4804090375957333),
  (4037653, 4043605, 2330295586174035, 4330532691594108),
  (4043605, 4049541, 1841497633129756, 3853553107834220)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4014629, 4019541, 4361037934056810, 5725021795681698) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4019541, 4025621, 3664749367009655, 5677514881815607) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4025621, 4031637, 3244566469731408, 5240427408136667) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4031637, 4037653, 2787131156830983, 4804090375957333) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4037653, 4043605, 2330295586174035, 4330532691594108) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4043605, 4049541, 1841497633129756, 3853553107834220) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C103
