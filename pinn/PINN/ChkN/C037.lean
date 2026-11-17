import PINN.Interval

/-! Pieces 222..227 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C037

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (995213, 1002092, -1780363162610397, -145919234730687),
  (1002092, 1008992, -1903332326706287, -274638570847763),
  (1008992, 1015949, -2029651090887285, -389850671364410),
  (1015949, 1022958, -2149542014679418, -501491803883296),
  (1022958, 1029963, -2250939661957157, -620244020162074),
  (1029963, 1037015, -2357791484366247, -721860713350309)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (995213, 1002092, -1780363162610397, -145919234730687) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1002092, 1008992, -1903332326706287, -274638570847763) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1008992, 1015949, -2029651090887285, -389850671364410) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1015949, 1022958, -2149542014679418, -501491803883296) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1022958, 1029963, -2250939661957157, -620244020162074) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1029963, 1037015, -2357791484366247, -721860713350309) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C037
