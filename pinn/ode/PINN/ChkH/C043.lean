import PINN.Interval

/-! Pieces 258..263 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C043

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1628374, 1635346, -4283778105175708, -2280892054176581),
  (1635346, 1642349, -4322592837354494, -2306455819325007),
  (1642349, 1649339, -4344061080233165, -2340382390269960),
  (1649339, 1656325, -4363654320194766, -2367011406776144),
  (1656325, 1660245, -3696181068547144, -3064238962428072),
  (1660245, 1667285, -4402351115976045, -2382374499932701)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1628374, 1635346, -4283778105175708, -2280892054176581) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1635346, 1642349, -4322592837354494, -2306455819325007) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1642349, 1649339, -4344061080233165, -2340382390269960) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1649339, 1656325, -4363654320194766, -2367011406776144) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1656325, 1660245, -3696181068547144, -3064238962428072) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1660245, 1667285, -4402351115976045, -2382374499932701) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C043
