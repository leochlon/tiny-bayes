import PINN.Interval

/-! Pieces 228..233 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C038

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1037015, 1044150, -2467428892118651, -809947049025758),
  (1044150, 1048576, -2041661519168513, -1387447968133793),
  (1048576, 1055744, -2609189119999907, -963585516251171),
  (1055744, 1062976, -2698525079810630, -1040863460096057),
  (1062976, 1070208, -2767311468396657, -1126315886991544),
  (1070208, 1077504, -2844026580486214, -1191400953863018)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1037015, 1044150, -2467428892118651, -809947049025758) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1044150, 1048576, -2041661519168513, -1387447968133793) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1048576, 1055744, -2609189119999907, -963585516251171) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1055744, 1062976, -2698525079810630, -1040863460096057) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1062976, 1070208, -2767311468396657, -1126315886991544) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1070208, 1077504, -2844026580486214, -1191400953863018) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C038
