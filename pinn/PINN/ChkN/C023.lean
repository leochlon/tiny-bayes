import PINN.Interval

/-! Pieces 138..143 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C023

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (499057, 504231, -5445198606716748, -3791973254719878),
  (504231, 509402, -5081297459551290, -3432767972781839),
  (509402, 514577, -4717503107556013, -3071050301173739),
  (514577, 519736, -4347824661496999, -2715735115163257),
  (519736, 524288, -3843400806158208, -2540167826474522),
  (524288, 529472, -3668970592614529, -2035778712711267)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (499057, 504231, -5445198606716748, -3791973254719878) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (504231, 509402, -5081297459551290, -3432767972781839) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (509402, 514577, -4717503107556013, -3071050301173739) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (514577, 519736, -4347824661496999, -2715735115163257) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (519736, 524288, -3843400806158208, -2540167826474522) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (524288, 529472, -3668970592614529, -2035778712711267) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C023
