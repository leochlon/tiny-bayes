import PINN.Interval

/-! Pieces 492..497 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C082

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3964544, 3980656, 2859316298415198, 4512006063549564),
  (3980656, 3996604, 3489160964436861, 5126239747293046),
  (3996604, 4012552, 4121779313174333, 5770414766869957),
  (4012552, 4019541, 5176538781310833, 5657734007251050),
  (4019541, 4035413, 5070331096486180, 6722809995429321),
  (4035413, 4051157, 5754526911151341, 7397062729148674)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3964544, 3980656, 2859316298415198, 4512006063549564) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3980656, 3996604, 3489160964436861, 5126239747293046) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3996604, 4012552, 4121779313174333, 5770414766869957) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (4012552, 4019541, 5176538781310833, 5657734007251050) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (4019541, 4035413, 5070331096486180, 6722809995429321) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (4035413, 4051157, 5754526911151341, 7397062729148674) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C082
