import PINN.Interval

/-! Pieces 126..131 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C021

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (436906, 442154, -9295175851354211, -7652897155741776),
  (442154, 447402, -9036454096493222, -7382334009755238),
  (447402, 452586, -8744766030894609, -7117173871554635),
  (452586, 457770, -8458579466446254, -6822118844915812),
  (457770, 462954, -8159139116107623, -6515150457520017),
  (462954, 468105, -7839455130321897, -6207880093591178)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (436906, 442154, -9295175851354211, -7652897155741776) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (442154, 447402, -9036454096493222, -7382334009755238) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (447402, 452586, -8744766030894609, -7117173871554635) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (452586, 457770, -8458579466446254, -6822118844915812) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (457770, 462954, -8159139116107623, -6515150457520017) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (462954, 468105, -7839455130321897, -6207880093591178) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C021
