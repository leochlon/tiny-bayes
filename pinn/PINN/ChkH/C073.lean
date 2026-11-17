import PINN.Interval

/-! Pieces 438..443 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C073

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2836893, 2843641, 827716409478329, 2827212681171538),
  (2843641, 2850428, 659903107596142, 2681469777302986),
  (2850428, 2857227, 499245929619927, 2527061111208354),
  (2857227, 2864022, 343126693462085, 2367857162796005),
  (2864022, 2870822, 184686086031573, 2211095098884299),
  (2870822, 2877601, 33885602369512, 2047528403715108)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2836893, 2843641, 827716409478329, 2827212681171538) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2843641, 2850428, 659903107596142, 2681469777302986) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2850428, 2857227, 499245929619927, 2527061111208354) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2857227, 2864022, 343126693462085, 2367857162796005) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2864022, 2870822, 184686086031573, 2211095098884299) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2870822, 2877601, 33885602369512, 2047528403715108) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C073
