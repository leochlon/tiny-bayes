import PINN.Interval

/-! Pieces 180..185 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C030

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1103239, 1110076, 5062688617545694, 7087834222481119),
  (1110076, 1116850, 4990844854436377, 6982579436928239),
  (1116850, 1123641, 4891585622764118, 6896507030133333),
  (1123641, 1130375, 4809929121124814, 6784805838279665),
  (1130375, 1135957, 5019059497518685, 6392414883779496),
  (1135957, 1142741, 4605989426730276, 6614770282926049)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1103239, 1110076, 5062688617545694, 7087834222481119) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1110076, 1116850, 4990844854436377, 6982579436928239) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1116850, 1123641, 4891585622764118, 6896507030133333) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1123641, 1130375, 4809929121124814, 6784805838279665) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1130375, 1135957, 5019059497518685, 6392414883779496) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1135957, 1142741, 4605989426730276, 6614770282926049) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C030
