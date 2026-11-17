import PINN.Interval

/-! Pieces 384..389 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C064

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2459349, 2472149, 2371860683220079, 4016832158208632),
  (2472149, 2484966, 2376860292782384, 4010193774267125),
  (2484966, 2497814, 2369939389350341, 4003899225192661),
  (2497814, 2510696, 2356599748740545, 3992163521401134),
  (2510696, 2523654, 2331841584226896, 3979647331287120),
  (2523654, 2534058, 2602167669275473, 3665068486742276)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2459349, 2472149, 2371860683220079, 4016832158208632) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2472149, 2484966, 2376860292782384, 4010193774267125) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2484966, 2497814, 2369939389350341, 4003899225192661) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2497814, 2510696, 2356599748740545, 3992163521401134) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2510696, 2523654, 2331841584226896, 3979647331287120) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2523654, 2534058, 2602167669275473, 3665068486742276) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C064
