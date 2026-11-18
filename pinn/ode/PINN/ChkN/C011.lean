import PINN.Interval

/-! Pieces 66..71 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C011

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (169531, 173862, 13991013347040543, 15643430446547022),
  (173862, 174762, 14364905164984476, 14538622129950817),
  (174762, 178986, 13269104228621408, 14894089489422747),
  (178986, 183210, 12620766887079532, 14273470841717795),
  (183210, 187370, 11972773591547575, 13608983861125161),
  (187370, 191530, 11288868798186063, 12945026218488078)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (169531, 173862, 13991013347040543, 15643430446547022) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (173862, 174762, 14364905164984476, 14538622129950817) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (174762, 178986, 13269104228621408, 14894089489422747) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (178986, 183210, 12620766887079532, 14273470841717795) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (183210, 187370, 11972773591547575, 13608983861125161) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (187370, 191530, 11288868798186063, 12945026218488078) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C011
