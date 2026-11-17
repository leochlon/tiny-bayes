import PINN.Interval

/-! Pieces 354..359 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C059

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2130847, 2142171, 974483107432079, 2626860375542433),
  (2142171, 2153423, 1061258790144036, 2682033191749659),
  (2153423, 2164846, 1113925377762867, 2771853288792815),
  (2164846, 2176227, 1197135897031018, 2831502329145645),
  (2176227, 2184533, 1636319895165037, 2515015565180041),
  (2184533, 2196053, 1310691728669090, 2963339856572166)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2130847, 2142171, 974483107432079, 2626860375542433) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2142171, 2153423, 1061258790144036, 2682033191749659) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2153423, 2164846, 1113925377762867, 2771853288792815) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2164846, 2176227, 1197135897031018, 2831502329145645) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2176227, 2184533, 1636319895165037, 2515015565180041) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2184533, 2196053, 1310691728669090, 2963339856572166) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C059
