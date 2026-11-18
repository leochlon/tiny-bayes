import PINN.Interval

/-! Pieces 18..23 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C003

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (23008, 24501, -26350091236070235, -24705701708769380),
  (24501, 26036, -24838763573085643, -23180127365916647),
  (26036, 27594, -23317900346425523, -21669952577856654),
  (27594, 29184, -21812491383183247, -20165222041871397),
  (29184, 30817, -20315454136979295, -18657446477083376),
  (30817, 32487, -18814191703374379, -17156277962369259)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (23008, 24501, -26350091236070235, -24705701708769380) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (24501, 26036, -24838763573085643, -23180127365916647) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (26036, 27594, -23317900346425523, -21669952577856654) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (27594, 29184, -21812491383183247, -20165222041871397) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (29184, 30817, -20315454136979295, -18657446477083376) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (30817, 32487, -18814191703374379, -17156277962369259) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C003
