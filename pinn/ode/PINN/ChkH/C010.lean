import PINN.Interval

/-! Pieces 60..65 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C010

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (341959, 348224, -4046414767394414, -2033364004267371),
  (348224, 349525, -3194666216678107, -3081700710150066),
  (349525, 355797, -4233565998973853, -2231985461280846),
  (355797, 362133, -4395614762876941, -2367788938627614),
  (362133, 368469, -4527725786506913, -2513318341267939),
  (368469, 374805, -4648788764208730, -2647899281683340)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (341959, 348224, -4046414767394414, -2033364004267371) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (348224, 349525, -3194666216678107, -3081700710150066) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (349525, 355797, -4233565998973853, -2231985461280846) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (355797, 362133, -4395614762876941, -2367788938627614) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (362133, 368469, -4527725786506913, -2513318341267939) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (368469, 374805, -4648788764208730, -2647899281683340) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C010
