import PINN.Interval

/-! Pieces 288..293 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C048

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1494314, 1503146, -1271637258278864, 351077383036642),
  (1503146, 1512106, -1246412275434217, 407693392136108),
  (1512106, 1521124, -1209929352479431, 449996733986331),
  (1521124, 1530117, -1160467142222705, 475572406641947),
  (1530117, 1539217, -1136355949509374, 523006020208443),
  (1539217, 1548285, -1089030142271574, 543736066127848)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1494314, 1503146, -1271637258278864, 351077383036642) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1503146, 1512106, -1246412275434217, 407693392136108) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1512106, 1521124, -1209929352479431, 449996733986331) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1521124, 1530117, -1160467142222705, 475572406641947) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1530117, 1539217, -1136355949509374, 523006020208443) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1539217, 1548285, -1089030142271574, 543736066127848) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C048
