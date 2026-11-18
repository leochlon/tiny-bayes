import PINN.Interval

/-! Pieces 558..563 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C093

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3628289, 3634809, 3951212571927506, 5960716169056310),
  (3634809, 3641341, 4163461099461935, 6179268208044505),
  (3641341, 3647894, 4372213604977844, 6399621562459779),
  (3647894, 3654374, 4606378787382959, 6589672616694428),
  (3654374, 3660911, 4800345904980734, 6815595255100494),
  (3660911, 3667455, 5008228694055909, 7025452545569946)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3628289, 3634809, 3951212571927506, 5960716169056310) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3634809, 3641341, 4163461099461935, 6179268208044505) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3641341, 3647894, 4372213604977844, 6399621562459779) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3647894, 3654374, 4606378787382959, 6589672616694428) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3654374, 3660911, 4800345904980734, 6815595255100494) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3660911, 3667455, 5008228694055909, 7025452545569946) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C093
