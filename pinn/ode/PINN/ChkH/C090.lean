import PINN.Interval

/-! Pieces 540..545 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C090

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3515029, 3521621, 217838652844970, 2244314109724263),
  (3521621, 3528174, 433392498844471, 2440648385147049),
  (3528174, 3534715, 642761663068269, 2645993454120234),
  (3534715, 3541266, 847819099998891, 2859642620350554),
  (3541266, 3547809, 1060096550257212, 3069849762721069),
  (3547809, 3554339, 1275443540111639, 3279700470955706)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3515029, 3521621, 217838652844970, 2244314109724263) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3521621, 3528174, 433392498844471, 2440648385147049) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3528174, 3534715, 642761663068269, 2645993454120234) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3534715, 3541266, 847819099998891, 2859642620350554) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3541266, 3547809, 1060096550257212, 3069849762721069) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3547809, 3554339, 1275443540111639, 3279700470955706) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C090
