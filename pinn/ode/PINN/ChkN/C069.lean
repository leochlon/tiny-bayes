import PINN.Interval

/-! Pieces 414..419 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C069

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2836987, 2850639, -116516592328294, 1521060859846214),
  (2850639, 2864409, -298607041747026, 1356591240340469),
  (2864409, 2878190, -472997289930728, 1175246832712808),
  (2878190, 2883584, 77721702279997, 372775898519294),
  (2883584, 2897408, -724500421006831, 919526602556940),
  (2897408, 2911232, -905708942570720, 728077546609616)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2836987, 2850639, -116516592328294, 1521060859846214) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2850639, 2864409, -298607041747026, 1356591240340469) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2864409, 2878190, -472997289930728, 1175246832712808) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2878190, 2883584, 77721702279997, 372775898519294) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2883584, 2897408, -724500421006831, 919526602556940) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2897408, 2911232, -905708942570720, 728077546609616) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C069
