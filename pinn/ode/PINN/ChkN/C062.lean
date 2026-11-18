import PINN.Interval

/-! Pieces 372..377 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C062

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2331728, 2343896, 2088424112111262, 3744470722107530),
  (2343896, 2356047, 2144879649545819, 3780638379554050),
  (2356047, 2359296, 2927964895637975, 3052405232891472),
  (2359296, 2371584, 2190546086776941, 3842060815613789),
  (2371584, 2383872, 2236826262257049, 3871805446180675),
  (2383872, 2396260, 2265961850032861, 3910555975386996)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2331728, 2343896, 2088424112111262, 3744470722107530) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2343896, 2356047, 2144879649545819, 3780638379554050) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2356047, 2359296, 2927964895637975, 3052405232891472) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2359296, 2371584, 2190546086776941, 3842060815613789) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2371584, 2383872, 2236826262257049, 3871805446180675) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2383872, 2396260, 2265961850032861, 3910555975386996) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C062
