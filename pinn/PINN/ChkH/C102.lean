import PINN.Interval

/-! Pieces 612..617 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C102

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3977307, 3983576, 6122592720065845, 8108489124457065),
  (3983576, 3989828, 5811971237593811, 7807275024670010),
  (3989828, 3996096, 5472011868919371, 7496867102361932),
  (3996096, 4002324, 5129410613161448, 7150983025703593),
  (4002324, 4008512, 4769037983048787, 6787514007741337),
  (4008512, 4014629, 4400930533585584, 6398398566709843)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3977307, 3983576, 6122592720065845, 8108489124457065) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3983576, 3989828, 5811971237593811, 7807275024670010) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3989828, 3996096, 5472011868919371, 7496867102361932) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3996096, 4002324, 5129410613161448, 7150983025703593) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4002324, 4008512, 4769037983048787, 6787514007741337) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4008512, 4014629, 4400930533585584, 6398398566709843) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C102
