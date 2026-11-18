import PINN.Interval

/-! Pieces 6..11 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C001

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (6960, 8176, -44879186877270788, -43236081964530377),
  (8176, 9408, -43322950938658461, -41683377372785550),
  (9408, 10672, -41773570489598259, -40116316599247231),
  (10672, 11952, -40210046321111080, -38558485913500590),
  (11952, 13248, -38654544667664933, -37009423260321125),
  (13248, 14576, -37108970699711257, -35449996562633606)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (6960, 8176, -44879186877270788, -43236081964530377) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (8176, 9408, -43322950938658461, -41683377372785550) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (9408, 10672, -41773570489598259, -40116316599247231) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (10672, 11952, -40210046321111080, -38558485913500590) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (11952, 13248, -38654544667664933, -37009423260321125) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (13248, 14576, -37108970699711257, -35449996562633606) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C001
