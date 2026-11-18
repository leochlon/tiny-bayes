import PINN.Interval

/-! Pieces 132..137 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C022

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (468105, 473262, -7520949262466291, -5881051940611397),
  (473262, 478444, -7197303232048094, -5539745390012812),
  (478444, 483592, -6848992646239470, -5208508071219960),
  (483592, 488758, -6509047091414390, -4857068195681146),
  (488758, 493893, -6149861750585470, -4515196703210429),
  (493893, 499057, -5802674192555304, -4152918007472235)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (468105, 473262, -7520949262466291, -5881051940611397) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (473262, 478444, -7197303232048094, -5539745390012812) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (478444, 483592, -6848992646239470, -5208508071219960) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (483592, 488758, -6509047091414390, -4857068195681146) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (488758, 493893, -6149861750585470, -4515196703210429) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (493893, 499057, -5802674192555304, -4152918007472235) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C022
