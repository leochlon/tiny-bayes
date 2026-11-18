import PINN.Interval

/-! Pieces 462..467 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C077

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2998357, 3005210, -2721087573879396, -711751326891552),
  (3005210, 3012059, -2847070710600818, -843887257100286),
  (3012059, 3018929, -2977310070805038, -966531662480905),
  (3018929, 3025781, -3093689164035078, -1097262499882736),
  (3025781, 3032650, -3217073706782008, -1214909350935892),
  (3032650, 3039475, -3320231631212476, -1346079878119043)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2998357, 3005210, -2721087573879396, -711751326891552) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3005210, 3012059, -2847070710600818, -843887257100286) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3012059, 3018929, -2977310070805038, -966531662480905) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3018929, 3025781, -3093689164035078, -1097262499882736) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3025781, 3032650, -3217073706782008, -1214909350935892) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3032650, 3039475, -3320231631212476, -1346079878119043) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C077
