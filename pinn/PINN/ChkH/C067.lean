import PINN.Interval

/-! Pieces 402..407 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C067

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2596211, 2603110, 5407752129282190, 7431307502047754),
  (2603110, 2609984, 5327839198823826, 7340369576537511),
  (2609984, 2616875, 5232104377399268, 7258189756749476),
  (2616875, 2621440, 5712523036434283, 6624302825079603),
  (2621440, 2628288, 5086197758005613, 7092945621388345),
  (2628288, 2635136, 4986857714801662, 6996860876983817)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2596211, 2603110, 5407752129282190, 7431307502047754) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2603110, 2609984, 5327839198823826, 7340369576537511) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2609984, 2616875, 5232104377399268, 7258189756749476) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2616875, 2621440, 5712523036434283, 6624302825079603) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2621440, 2628288, 5086197758005613, 7092945621388345) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2628288, 2635136, 4986857714801662, 6996860876983817) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C067
