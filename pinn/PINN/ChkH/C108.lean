import PINN.Interval

/-! Pieces 648..651 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C108

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4175889, 4180924, -14987736715743330, -12989169907510970),
  (4180924, 4185941, -15897654868035720, -13888397676710763),
  (4185941, 4190906, -16812102885268596, -14813200368960794),
  (4190906, 4194304, -17174122183447677, -16025454260731511)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4175889, 4180924, -14987736715743330, -12989169907510970) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4180924, 4185941, -15897654868035720, -13888397676710763) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4185941, 4190906, -16812102885268596, -14813200368960794) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4190906, 4194304, -17174122183447677, -16025454260731511) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, Bool.and_self, Bool.and_true]

end PINN.ChkH.C108
