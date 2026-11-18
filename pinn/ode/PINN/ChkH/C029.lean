import PINN.Interval

/-! Pieces 174..179 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C029

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1062272, 1069120, 5502439695716692, 7511920196436822),
  (1069120, 1075968, 5440945764180589, 7454299116247307),
  (1075968, 1082821, 5372642859565192, 7392980017507416),
  (1082821, 1089670, 5302011160056943, 7323723870533631),
  (1089670, 1096449, 5245889997757869, 7230782566670755),
  (1096449, 1103239, 5162140487089980, 7156487998384594)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1062272, 1069120, 5502439695716692, 7511920196436822) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1069120, 1075968, 5440945764180589, 7454299116247307) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1075968, 1082821, 5372642859565192, 7392980017507416) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1082821, 1089670, 5302011160056943, 7323723870533631) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1089670, 1096449, 5245889997757869, 7230782566670755) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1096449, 1103239, 5162140487089980, 7156487998384594) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C029
