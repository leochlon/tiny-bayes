import PINN.Interval

/-! Pieces 252..257 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C042

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1586688, 1593600, -3995173543016786, -1998859041305681),
  (1593600, 1600576, -4069608205289861, -2041266311481623),
  (1600576, 1607509, -4109367723766543, -2109862550898496),
  (1607509, 1614410, -4147562691665554, -2170768585344673),
  (1614410, 1621393, -4213935466382805, -2195102951335423),
  (1621393, 1628374, -4252183780481033, -2239178105505865)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1586688, 1593600, -3995173543016786, -1998859041305681) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1593600, 1600576, -4069608205289861, -2041266311481623) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1600576, 1607509, -4109367723766543, -2109862550898496) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1607509, 1614410, -4147562691665554, -2170768585344673) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1614410, 1621393, -4213935466382805, -2195102951335423) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1621393, 1628374, -4252183780481033, -2239178105505865) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C042
