import PINN.Interval

/-! Pieces 420..425 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C070

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2911232, 2925115, -1096492409228942, 539963329593900),
  (2925115, 2939084, -1293371017788610, 351133246030078),
  (2939084, 2953156, -1495188885823096, 160459087149323),
  (2953156, 2967208, -1685570740783999, -46237183843590),
  (2967208, 2970965, -1070327841899171, -914343834173243),
  (2970965, 2985173, -1949211746866612, -291455281632438)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2911232, 2925115, -1096492409228942, 539963329593900) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2925115, 2939084, -1293371017788610, 351133246030078) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2939084, 2953156, -1495188885823096, 160459087149323) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2953156, 2967208, -1685570740783999, -46237183843590) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2967208, 2970965, -1070327841899171, -914343834173243) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2970965, 2985173, -1949211746866612, -291455281632438) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C070
