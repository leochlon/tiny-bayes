import PINN.Interval

/-! Pieces 408..413 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C068

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2635136, 2641984, 4884245731348465, 6897407800192032),
  (2641984, 2648832, 4778429832375860, 6794652878339707),
  (2648832, 2655685, 4667859106288171, 6690240682288611),
  (2655685, 2662534, 4556948974677242, 6579905645037387),
  (2662534, 2669313, 4462547654843211, 6448254067234887),
  (2669313, 2676103, 4342795822736699, 6337094197624746)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2635136, 2641984, 4884245731348465, 6897407800192032) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2641984, 2648832, 4778429832375860, 6794652878339707) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2648832, 2655685, 4667859106288171, 6690240682288611) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2655685, 2662534, 4556948974677242, 6579905645037387) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2662534, 2669313, 4462547654843211, 6448254067234887) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2669313, 2676103, 4342795822736699, 6337094197624746) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C068
