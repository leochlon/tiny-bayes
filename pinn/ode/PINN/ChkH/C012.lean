import PINN.Interval

/-! Pieces 72..77 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C012

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (413401, 419920, -5244776494166002, -3228595431514990),
  (419920, 426422, -5271453646997548, -3279892180954822),
  (426422, 432974, -5307370337779985, -3299292803521379),
  (432974, 436906, -4678616888590614, -3956103176567984),
  (436906, 443498, -5329311226588279, -3319087149141505),
  (443498, 450090, -5328741818211471, -3316591502513305)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (413401, 419920, -5244776494166002, -3228595431514990) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (419920, 426422, -5271453646997548, -3279892180954822) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (426422, 432974, -5307370337779985, -3299292803521379) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (432974, 436906, -4678616888590614, -3956103176567984) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (436906, 443498, -5329311226588279, -3319087149141505) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (443498, 450090, -5328741818211471, -3316591502513305) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C012
