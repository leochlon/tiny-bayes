import PINN.Interval

/-! Pieces 426..431 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C071

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2756259, 2763046, 2632937263836218, 4650228926305549),
  (2763046, 2769845, 2482330390103212, 4507622806608031),
  (2769845, 2776640, 2334766962354525, 4358769679257563),
  (2776640, 2783440, 2183415820116287, 4210828349539795),
  (2783440, 2790219, 2038165611183316, 4054591884283661),
  (2790219, 2796202, 2110062732756688, 3697168784961225)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2756259, 2763046, 2632937263836218, 4650228926305549) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2763046, 2769845, 2482330390103212, 4507622806608031) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2769845, 2776640, 2334766962354525, 4358769679257563) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2776640, 2783440, 2183415820116287, 4210828349539795) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2783440, 2790219, 2038165611183316, 4054591884283661) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2790219, 2796202, 2110062732756688, 3697168784961225) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C071
