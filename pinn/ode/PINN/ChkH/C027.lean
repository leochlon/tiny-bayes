import PINN.Interval

/-! Pieces 162..167 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C027

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (981802, 988714, 5772239378779771, 7792780160067784),
  (988714, 995612, 5789043434609048, 7793424471806815),
  (995612, 1002542, 5785928855056245, 7801396755971345),
  (1002542, 1009465, 5781696077439892, 7797969728826343),
  (1009465, 1016339, 5783784447438179, 7775883316459145),
  (1016339, 1023265, 5750374781939199, 7777097113748490)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (981802, 988714, 5772239378779771, 7792780160067784) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (988714, 995612, 5789043434609048, 7793424471806815) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (995612, 1002542, 5785928855056245, 7801396755971345) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1002542, 1009465, 5781696077439892, 7797969728826343) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1009465, 1016339, 5783784447438179, 7775883316459145) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1016339, 1023265, 5750374781939199, 7777097113748490) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C027
