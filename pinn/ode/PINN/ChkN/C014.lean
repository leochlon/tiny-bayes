import PINN.Interval

/-! Pieces 84..89 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C014

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (240399, 244519, 1965876402121298, 3612786567431852),
  (244519, 248650, 1264339895034348, 2905616550319804),
  (248650, 252814, 565504555789063, 2212437897789540),
  (252814, 257004, -121513467362507, 1525445223028286),
  (257004, 261220, -796603274692976, 848765281787622),
  (261220, 262144, -474757026719240, -283343103655222)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (240399, 244519, 1965876402121298, 3612786567431852) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (244519, 248650, 1264339895034348, 2905616550319804) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (248650, 252814, 565504555789063, 2212437897789540) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (252814, 257004, -121513467362507, 1525445223028286) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (257004, 261220, -796603274692976, 848765281787622) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (261220, 262144, -474757026719240, -283343103655222) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C014
