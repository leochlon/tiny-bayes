import PINN.Interval

/-! Pieces 366..371 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C061

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2354284, 2359296, 6339203062011558, 7406755030491438),
  (2359296, 2366208, 5920006540304827, 7924882104595946),
  (2366208, 2373120, 5975605014254610, 7976753905188306),
  (2373120, 2380032, 6027320135802722, 8024679482067037),
  (2380032, 2386944, 6075104893099245, 8068618025386182),
  (2386944, 2393885, 6110561954929800, 8117036622333067)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2354284, 2359296, 6339203062011558, 7406755030491438) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2359296, 2366208, 5920006540304827, 7924882104595946) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2366208, 2373120, 5975605014254610, 7976753905188306) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2373120, 2380032, 6027320135802722, 8024679482067037) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2380032, 2386944, 6075104893099245, 8068618025386182) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2386944, 2393885, 6110561954929800, 8117036622333067) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C061
