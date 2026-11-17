import PINN.Interval

/-! Pieces 342..347 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C057

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2191317, 2198101, 3571671919939727, 5568276455917318),
  (2198101, 2204885, 3699405652017037, 5694513216899083),
  (2204885, 2211669, 3825123426016514, 5818624028280277),
  (2211669, 2218493, 3937674420450310, 5952302531095542),
  (2218493, 2225275, 4071412400281091, 6060224179382050),
  (2225275, 2232106, 4176768477828383, 6191924826094134)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2191317, 2198101, 3571671919939727, 5568276455917318) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2198101, 2204885, 3699405652017037, 5694513216899083) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2204885, 2211669, 3825123426016514, 5818624028280277) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2211669, 2218493, 3937674420450310, 5952302531095542) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2218493, 2225275, 4071412400281091, 6060224179382050) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2225275, 2232106, 4176768477828383, 6191924826094134) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C057
