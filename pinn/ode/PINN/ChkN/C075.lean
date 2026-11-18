import PINN.Interval

/-! Pieces 450..455 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C075

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3320490, 3336874, -6155013100827164, -4518667958875317),
  (3336874, 3353514, -6270714381431215, -4615495136477775),
  (3353514, 3370288, -6361925014615971, -4712788142318132),
  (3370288, 3387171, -6437550131827630, -4798919344534805),
  (3387171, 3404313, -6513439687801329, -4856746604985804),
  (3404313, 3407872, -5757669294396010, -5678722925506873)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3320490, 3336874, -6155013100827164, -4518667958875317) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3336874, 3353514, -6270714381431215, -4615495136477775) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3353514, 3370288, -6361925014615971, -4712788142318132) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3370288, 3387171, -6437550131827630, -4798919344534805) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3387171, 3404313, -6513439687801329, -4856746604985804) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3404313, 3407872, -5757669294396010, -5678722925506873) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C075
