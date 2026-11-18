import PINN.Interval

/-! Pieces 276..281 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C046

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1398101, 1406549, -1844028038386981, -203888253501895),
  (1406549, 1414997, -1779915175022424, -153270350588948),
  (1414997, 1423445, -1717095814747103, -103978677132601),
  (1423445, 1432047, -1684045956652729, -26746565833381),
  (1432047, 1440604, -1614621383409498, 11751485772588),
  (1440604, 1449281, -1577363923507338, 79653507063743)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1398101, 1406549, -1844028038386981, -203888253501895) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1406549, 1414997, -1779915175022424, -153270350588948) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1414997, 1423445, -1717095814747103, -103978677132601) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1423445, 1432047, -1684045956652729, -26746565833381) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1432047, 1440604, -1614621383409498, 11751485772588) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1440604, 1449281, -1577363923507338, 79653507063743) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C046
