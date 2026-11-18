import PINN.Interval

/-! Pieces 114..119 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C019

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (675631, 682034, -350188798908754, 1660272201799549),
  (682034, 688415, -140767814352565, 1854322256968806),
  (688415, 694812, 57094187986107, 2059170385865635),
  (694812, 699050, 764076901552264, 1686575851166706),
  (699050, 705450, 392625490500767, 2391424493521279),
  (705450, 711850, 593888860176746, 2589516339997541)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (675631, 682034, -350188798908754, 1660272201799549) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (682034, 688415, -140767814352565, 1854322256968806) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (688415, 694812, 57094187986107, 2059170385865635) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (694812, 699050, 764076901552264, 1686575851166706) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (699050, 705450, 392625490500767, 2391424493521279) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (705450, 711850, 593888860176746, 2589516339997541) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C019
