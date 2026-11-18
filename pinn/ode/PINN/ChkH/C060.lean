import PINN.Interval

/-! Pieces 360..365 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C060

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2313009, 2319879, 5462964929065724, 7466909031678485),
  (2319879, 2326731, 5547855670815074, 7538328090014130),
  (2326731, 2333600, 5619116524220497, 7616309006627548),
  (2333600, 2340525, 5676181618163645, 7702089416075257),
  (2340525, 2347417, 5755386219627135, 7758619685554618),
  (2347417, 2354284, 5827988810535123, 7813731712523723)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2313009, 2319879, 5462964929065724, 7466909031678485) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2319879, 2326731, 5547855670815074, 7538328090014130) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2326731, 2333600, 5619116524220497, 7616309006627548) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2333600, 2340525, 5676181618163645, 7702089416075257) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2340525, 2347417, 5755386219627135, 7758619685554618) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2347417, 2354284, 5827988810535123, 7813731712523723) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C060
