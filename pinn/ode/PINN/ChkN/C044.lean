import PINN.Interval

/-! Pieces 264..269 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C044

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1302906, 1310720, -2487837527509972, -953498499558607),
  (1310720, 1318848, -2485856577406715, -839041826976473),
  (1318848, 1326976, -2420234432351231, -784745499463204),
  (1326976, 1335168, -2366490921526973, -717316409091549),
  (1335168, 1343403, -2307927502545199, -653539736543252),
  (1343403, 1351629, -2238684587255893, -600187355059426)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1302906, 1310720, -2487837527509972, -953498499558607) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1310720, 1318848, -2485856577406715, -839041826976473) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1318848, 1326976, -2420234432351231, -784745499463204) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1326976, 1335168, -2366490921526973, -717316409091549) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1335168, 1343403, -2307927502545199, -653539736543252) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1343403, 1351629, -2238684587255893, -600187355059426) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C044
