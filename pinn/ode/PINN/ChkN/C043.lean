import PINN.Interval

/-! Pieces 258..263 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C043

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1254918, 1262874, -2870625150087534, -1221551663542696),
  (1262874, 1270816, -2813188159491448, -1179199233003320),
  (1270816, 1278843, -2773600901578218, -1114628037948072),
  (1278843, 1286813, -2703100054349173, -1077329662870591),
  (1286813, 1294844, -2654980815446703, -1014675934609080),
  (1294844, 1302906, -2598870238119354, -956858601597630)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1254918, 1262874, -2870625150087534, -1221551663542696) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1262874, 1270816, -2813188159491448, -1179199233003320) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1270816, 1278843, -2773600901578218, -1114628037948072) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1278843, 1286813, -2703100054349173, -1077329662870591) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1286813, 1294844, -2654980815446703, -1014675934609080) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1294844, 1302906, -2598870238119354, -956858601597630) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C043
