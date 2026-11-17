import PINN.Interval

/-! Pieces 282..287 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C047

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1449281, 1457978, -1522478518469231, 127370143175490),
  (1457978, 1466680, -1466356984309592, 170463358619763),
  (1466680, 1475419, -1418010413097289, 217927377546977),
  (1475419, 1484224, -1376378815705529, 268949929267066),
  (1484224, 1485482, -547448353371323, -508535306316491),
  (1485482, 1494314, -1321725705423275, 316072055441848)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1449281, 1457978, -1522478518469231, 127370143175490) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1457978, 1466680, -1466356984309592, 170463358619763) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1466680, 1475419, -1418010413097289, 217927377546977) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1475419, 1484224, -1376378815705529, 268949929267066) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1484224, 1485482, -547448353371323, -508535306316491) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1485482, 1494314, -1321725705423275, 316072055441848) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C047
