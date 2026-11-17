import PINN.Interval

/-! Pieces 486..491 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C081

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3877802, 3894151, -145643725525667, 1484163351197769),
  (3894151, 3910483, 374252895780304, 2012543702779318),
  (3910483, 3926741, 918209174403179, 2555633888694019),
  (3926741, 3932160, 1955583337894632, 2264277163020069),
  (3932160, 3948416, 1665580311990854, 3318632650372786),
  (3948416, 3964544, 2258329350813365, 3901875165107110)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3877802, 3894151, -145643725525667, 1484163351197769) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3894151, 3910483, 374252895780304, 2012543702779318) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3910483, 3926741, 918209174403179, 2555633888694019) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3926741, 3932160, 1955583337894632, 2264277163020069) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3932160, 3948416, 1665580311990854, 3318632650372786) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3948416, 3964544, 2258329350813365, 3901875165107110) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C081
