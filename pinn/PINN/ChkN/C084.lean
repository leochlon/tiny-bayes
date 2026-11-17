import PINN.Interval

/-! Pieces 504..507 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C084

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4137770, 4153007, 10589372313817819, 12221529902062212),
  (4153007, 4168332, 11363884936256494, 13020826891552008),
  (4168332, 4183549, 12170162094507234, 13819598957341598),
  (4183549, 4194304, 13190690395709922, 14189033775632258)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (4137770, 4153007, 10589372313817819, 12221529902062212) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (4153007, 4168332, 11363884936256494, 13020826891552008) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (4168332, 4183549, 12170162094507234, 13819598957341598) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (4183549, 4194304, 13190690395709922, 14189033775632258) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, Bool.and_self, Bool.and_true]

end PINN.ChkN.C084
