import PINN.Interval

/-! Pieces 360..365 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C060

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2196053, 2207573, 1387439079843596, 3027767285944692),
  (2207573, 2219134, 1457669169073993, 3097056970923893),
  (2219134, 2230782, 1521056181740002, 3171659901387915),
  (2230782, 2242510, 1584657298031894, 3244280232865676),
  (2242510, 2254225, 1659798177892582, 3302559693857938),
  (2254225, 2265971, 1727358239473882, 3364924737585105)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2196053, 2207573, 1387439079843596, 3027767285944692) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2207573, 2219134, 1457669169073993, 3097056970923893) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2219134, 2230782, 1521056181740002, 3171659901387915) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2230782, 2242510, 1584657298031894, 3244280232865676) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2242510, 2254225, 1659798177892582, 3302559693857938) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2254225, 2265971, 1727358239473882, 3364924737585105) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C060
