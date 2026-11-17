import PINN.Interval

/-! Pieces 372..377 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C062

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2393885, 2400793, 6160003306751551, 8143380648903215),
  (2400793, 2407782, 6172621822606852, 8198580052854332),
  (2407782, 2414771, 6204621040186090, 8226449126901831),
  (2414771, 2421751, 6235134270736948, 8247346973670142),
  (2421751, 2428761, 6250149113621789, 8275344185368828),
  (2428761, 2435759, 6272972506218679, 8287023184382305)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2393885, 2400793, 6160003306751551, 8143380648903215) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2400793, 2407782, 6172621822606852, 8198580052854332) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2407782, 2414771, 6204621040186090, 8226449126901831) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2414771, 2421751, 6235134270736948, 8247346973670142) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2421751, 2428761, 6250149113621789, 8275344185368828) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2428761, 2435759, 6272972506218679, 8287023184382305) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C062
