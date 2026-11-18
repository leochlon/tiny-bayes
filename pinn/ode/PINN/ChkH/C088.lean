import PINN.Interval

/-! Pieces 528..533 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C088

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3441198, 3447849, -1891098410755979, 122848811814708),
  (3447849, 3454515, -1724481511533706, 302910644964440),
  (3454515, 3461119, -1532389067267459, 463918004840779),
  (3461119, 3467718, -1354101505276667, 644298311712064),
  (3467718, 3474332, -1177501673945390, 833834387504813),
  (3474332, 3480951, -994549466925172, 1024409463243007)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3441198, 3447849, -1891098410755979, 122848811814708) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3447849, 3454515, -1724481511533706, 302910644964440) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3454515, 3461119, -1532389067267459, 463918004840779) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3461119, 3467718, -1354101505276667, 644298311712064) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3467718, 3474332, -1177501673945390, 833834387504813) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3474332, 3480951, -994549466925172, 1024409463243007) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C088
