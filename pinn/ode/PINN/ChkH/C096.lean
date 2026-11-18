import PINN.Interval

/-! Pieces 576..581 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C096

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3742148, 3748760, 7313971249425075, 9327439109315760),
  (3748760, 3755372, 7470783545402593, 9478544187442578),
  (3755372, 3757397, 8461926077100063, 8681413097520038),
  (3757397, 3764053, 7653506892167230, 9679016077191715),
  (3764053, 3770709, 7795927915380259, 9814796063505696),
  (3770709, 3777365, 7931029839749896, 9942877706725339)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3742148, 3748760, 7313971249425075, 9327439109315760) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3748760, 3755372, 7470783545402593, 9478544187442578) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3755372, 3757397, 8461926077100063, 8681413097520038) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3757397, 3764053, 7653506892167230, 9679016077191715) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3764053, 3770709, 7795927915380259, 9814796063505696) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3770709, 3777365, 7931029839749896, 9942877706725339) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C096
