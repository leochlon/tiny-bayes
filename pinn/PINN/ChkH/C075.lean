import PINN.Interval

/-! Pieces 450..455 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C075

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2917485, 2924274, -1028547645342276, 979715054067237),
  (2924274, 2931022, -1166514172335455, 816026738654258),
  (2931022, 2937809, -1326070293676343, 676584163822637),
  (2937809, 2944608, -1476889039810410, 530107123431696),
  (2944608, 2951403, -1621641751410565, 380490178475929),
  (2951403, 2958203, -1767086760263848, 234844531572086)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2917485, 2924274, -1028547645342276, 979715054067237) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2924274, 2931022, -1166514172335455, 816026738654258) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2931022, 2937809, -1326070293676343, 676584163822637) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2937809, 2944608, -1476889039810410, 530107123431696) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2944608, 2951403, -1621641751410565, 380490178475929) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2951403, 2958203, -1767086760263848, 234844531572086) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C075
