import PINN.Interval

/-! Pieces 204..209 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C034

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (880277, 886741, 967486706965427, 2615871066831740),
  (886741, 893205, 797927998733571, 2437725094230587),
  (893205, 899669, 629002450884041, 2259800628075432),
  (899669, 906157, 455107564927516, 2087913930929227),
  (906157, 912714, 270675794238419, 1926670449211296),
  (912714, 919246, 110240763416067, 1743600577593969)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (880277, 886741, 967486706965427, 2615871066831740) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (886741, 893205, 797927998733571, 2437725094230587) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (893205, 899669, 629002450884041, 2259800628075432) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (899669, 906157, 455107564927516, 2087913930929227) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (906157, 912714, 270675794238419, 1926670449211296) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (912714, 919246, 110240763416067, 1743600577593969) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C034
