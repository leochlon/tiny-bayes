import PINN.Interval

/-! Pieces 210..215 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C035

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (919246, 925800, -59185734834549, 1573773327980252),
  (925800, 932367, -224392673377174, 1403730733481955),
  (932367, 939010, -402410469921194, 1249827860278622),
  (939010, 945681, -566973820141104, 1086226424123386),
  (945681, 952346, -720123213681942, 917697190367250),
  (952346, 959051, -880443297747998, 763157757104748)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (919246, 925800, -59185734834549, 1573773327980252) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (925800, 932367, -224392673377174, 1403730733481955) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (932367, 939010, -402410469921194, 1249827860278622) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (939010, 945681, -566973820141104, 1086226424123386) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (945681, 952346, -720123213681942, 917697190367250) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (952346, 959051, -880443297747998, 763157757104748) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C035
