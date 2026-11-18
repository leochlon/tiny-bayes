import PINN.Interval

/-! Pieces 636..641 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C106

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4112426, 4117930, -5359467244904576, -3342053514488266),
  (4117930, 4123370, -6064211768875878, -4063030970957654),
  (4123370, 4128810, -6805906543720131, -4782287187016364),
  (4128810, 4134182, -7544215023568934, -5539443294917241),
  (4134182, 4139525, -8309485933811885, -6299570875108178),
  (4139525, 4144821, -9085311268970951, -7082048421895794)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4112426, 4117930, -5359467244904576, -3342053514488266) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4117930, 4123370, -6064211768875878, -4063030970957654) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4123370, 4128810, -6805906543720131, -4782287187016364) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4128810, 4134182, -7544215023568934, -5539443294917241) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4134182, 4139525, -8309485933811885, -6299570875108178) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4139525, 4144821, -9085311268970951, -7082048421895794) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C106
