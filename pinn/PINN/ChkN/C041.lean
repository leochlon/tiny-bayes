import PINN.Interval

/-! Pieces 246..251 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C041

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1166669, 1174416, -3215534661878675, -1565844141264551),
  (1174416, 1182155, -3200938954015175, -1560986063321087),
  (1182155, 1189957, -3196297659054969, -1536567329162399),
  (1189957, 1197715, -3164524303356661, -1530195657133927),
  (1197715, 1205521, -3147688158236079, -1500345565530810),
  (1205521, 1213316, -3114399501683228, -1478802843597728)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1166669, 1174416, -3215534661878675, -1565844141264551) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1174416, 1182155, -3200938954015175, -1560986063321087) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1182155, 1189957, -3196297659054969, -1536567329162399) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1189957, 1197715, -3164524303356661, -1530195657133927) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1197715, 1205521, -3147688158236079, -1500345565530810) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1205521, 1213316, -3114399501683228, -1478802843597728) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C041
