import PINN.Interval

/-! Pieces 24..29 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C004

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (131481, 137737, 3818721286158366, 5838068706045226),
  (137737, 143956, 3699331094852009, 5718520030538651),
  (143956, 150152, 3554456185854305, 5579163881221734),
  (150152, 156305, 3396651951692148, 5412658695992411),
  (156305, 162433, 3216874213490573, 5232701976796066),
  (162433, 168549, 3017839299482418, 5040027496373615)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (131481, 137737, 3818721286158366, 5838068706045226) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (137737, 143956, 3699331094852009, 5718520030538651) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (143956, 150152, 3554456185854305, 5579163881221734) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (150152, 156305, 3396651951692148, 5412658695992411) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (156305, 162433, 3216874213490573, 5232701976796066) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (162433, 168549, 3017839299482418, 5040027496373615) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C004
