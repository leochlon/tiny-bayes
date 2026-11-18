import PINN.Interval

/-! Pieces 120..125 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C020

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (409544, 414941, -10369063624090315, -8725801898019126),
  (414941, 420304, -10202816478146388, -8559134886689058),
  (420304, 425621, -10010057012557622, -8374628775398620),
  (425621, 430911, -9801389002782082, -8165202225215723),
  (430911, 436202, -9580761803489104, -7928567420272968),
  (436202, 436906, -8645775571613716, -8587611352967026)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (409544, 414941, -10369063624090315, -8725801898019126) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (414941, 420304, -10202816478146388, -8559134886689058) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (420304, 425621, -10010057012557622, -8374628775398620) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (425621, 430911, -9801389002782082, -8165202225215723) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (430911, 436202, -9580761803489104, -7928567420272968) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (436202, 436906, -8645775571613716, -8587611352967026) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C020
