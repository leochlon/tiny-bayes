import PINN.Interval

/-! Pieces 234..239 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C039

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1077504, 1084811, -2902848308735036, -1261988703331729),
  (1084811, 1092103, -2949323139131579, -1331942225081305),
  (1092103, 1099468, -3009066803542051, -1376245563300706),
  (1099468, 1106880, -3056970427944829, -1420488495376829),
  (1106880, 1114377, -3107377285297292, -1450326315537590),
  (1114377, 1121878, -3133936070329516, -1491929635648535)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1077504, 1084811, -2902848308735036, -1261988703331729) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1084811, 1092103, -2949323139131579, -1331942225081305) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1092103, 1099468, -3009066803542051, -1376245563300706) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1099468, 1106880, -3056970427944829, -1420488495376829) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1106880, 1114377, -3107377285297292, -1450326315537590) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1114377, 1121878, -3133936070329516, -1491929635648535) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C039
