import PINN.Interval

/-! Pieces 198..203 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C033

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (843588, 849964, 1942446222032948, 3587446133019634),
  (849964, 856299, 1790684319334632, 3410404525979521),
  (856299, 862661, 1620745280396423, 3247283979114585),
  (862661, 869021, 1455865995768724, 3074903750443885),
  (869021, 873813, 1642778152678530, 2590189291294403),
  (873813, 880277, 1137242408175619, 2793781899946371)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (843588, 849964, 1942446222032948, 3587446133019634) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (849964, 856299, 1790684319334632, 3410404525979521) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (856299, 862661, 1620745280396423, 3247283979114585) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (862661, 869021, 1455865995768724, 3074903750443885) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (869021, 873813, 1642778152678530, 2590189291294403) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (873813, 880277, 1137242408175619, 2793781899946371) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C033
