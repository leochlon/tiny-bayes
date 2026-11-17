import PINN.Interval

/-! Pieces 642..647 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C107

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4144821, 4150087, -9882429681301594, -7875188692292607),
  (4150087, 4155312, -10692588027795375, -8687775468944110),
  (4155312, 4160490, -11515432442443795, -9517592270794580),
  (4160490, 4165641, -12360223705975158, -10356470284710309),
  (4165641, 4170791, -13232160384008268, -11207265695161540),
  (4170791, 4175889, -14105791939794110, -12090770200338259)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4144821, 4150087, -9882429681301594, -7875188692292607) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4150087, 4155312, -10692588027795375, -8687775468944110) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4155312, 4160490, -11515432442443795, -9517592270794580) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4160490, 4165641, -12360223705975158, -10356470284710309) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4165641, 4170791, -13232160384008268, -11207265695161540) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4170791, 4175889, -14105791939794110, -12090770200338259) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C107
