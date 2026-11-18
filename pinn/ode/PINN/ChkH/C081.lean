import PINN.Interval

/-! Pieces 486..491 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C081

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3159680, 3166656, -4808808626364972, -2813363927544046),
  (3166656, 3173696, -4862076504192679, -2833383394245788),
  (3173696, 3180716, -4886249628581693, -2872178775821242),
  (3180716, 3187675, -4893448955290379, -2916976218963655),
  (3187675, 3194685, -4926695611203402, -2925005485270039),
  (3194685, 3201738, -4952663968417237, -2929655014952178)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3159680, 3166656, -4808808626364972, -2813363927544046) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3166656, 3173696, -4862076504192679, -2833383394245788) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3173696, 3180716, -4886249628581693, -2872178775821242) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3180716, 3187675, -4893448955290379, -2916976218963655) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3187675, 3194685, -4926695611203402, -2925005485270039) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3194685, 3201738, -4952663968417237, -2929655014952178) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C081
