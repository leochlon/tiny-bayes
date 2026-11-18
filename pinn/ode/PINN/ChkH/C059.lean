import PINN.Interval

/-! Pieces 354..359 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C059

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2271914, 2278762, 4922142610342121, 6930945032402795),
  (2278762, 2285610, 5021189121881630, 7027311341711239),
  (2285610, 2292458, 5117166241454203, 7120519388585554),
  (2292458, 2299306, 5210009563191826, 7210501940537620),
  (2299306, 2306159, 5298103389101652, 7298786659991094),
  (2306159, 2313009, 5385527999194661, 7381153941864652)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2271914, 2278762, 4922142610342121, 6930945032402795) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2278762, 2285610, 5021189121881630, 7027311341711239) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2285610, 2292458, 5117166241454203, 7120519388585554) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2292458, 2299306, 5210009563191826, 7210501940537620) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2299306, 2306159, 5298103389101652, 7298786659991094) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2306159, 2313009, 5385527999194661, 7381153941864652) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C059
