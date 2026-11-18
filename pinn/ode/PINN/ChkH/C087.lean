import PINN.Interval

/-! Pieces 522..527 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C087

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3401588, 3407872, -2721518207411332, -945490901674713),
  (3407872, 3414592, -2702216741352336, -675751839241830),
  (3414592, 3421248, -2533454019261986, -538312896309025),
  (3421248, 3427904, -2379455533716017, -378805755222917),
  (3427904, 3434560, -2221124003967950, -215066054807929),
  (3434560, 3441198, -2053582560869555, -52623413343510)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3401588, 3407872, -2721518207411332, -945490901674713) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3407872, 3414592, -2702216741352336, -675751839241830) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3414592, 3421248, -2533454019261986, -538312896309025) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3421248, 3427904, -2379455533716017, -378805755222917) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3427904, 3434560, -2221124003967950, -215066054807929) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3434560, 3441198, -2053582560869555, -52623413343510) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C087
