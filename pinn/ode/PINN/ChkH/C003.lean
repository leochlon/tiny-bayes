import PINN.Interval

/-! Pieces 18..23 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C003

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (93525, 99733, 3914845372966775, 5906024876871362),
  (99733, 106069, 3972440135457160, 6001347163813565),
  (106069, 112469, 4010074352676159, 6038378920757379),
  (112469, 118855, 4015992997867004, 6031811265008036),
  (118855, 125188, 3981761073632084, 5996053473905903),
  (125188, 131481, 3913958576216562, 5931441022758802)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (93525, 99733, 3914845372966775, 5906024876871362) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (99733, 106069, 3972440135457160, 6001347163813565) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (106069, 112469, 4010074352676159, 6038378920757379) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (112469, 118855, 4015992997867004, 6031811265008036) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (118855, 125188, 3981761073632084, 5996053473905903) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (125188, 131481, 3913958576216562, 5931441022758802) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C003
