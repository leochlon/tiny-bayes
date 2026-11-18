import PINN.Interval

/-! Pieces 96..101 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C016

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (562925, 569303, -3639366248728855, -1649939036067494),
  (569303, 575674, -3479927270593853, -1491584594282074),
  (575674, 582070, -3324431344627260, -1318893860797011),
  (582070, 588487, -3162697137326179, -1141994104367595),
  (588487, 594826, -2967360569833104, -991536313007583),
  (594826, 601207, -2804312779377466, -801799756080542)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (562925, 569303, -3639366248728855, -1649939036067494) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (569303, 575674, -3479927270593853, -1491584594282074) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (575674, 582070, -3324431344627260, -1318893860797011) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (582070, 588487, -3162697137326179, -1141994104367595) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (588487, 594826, -2967360569833104, -991536313007583) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (594826, 601207, -2804312779377466, -801799756080542) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C016
