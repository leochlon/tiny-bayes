import PINN.Interval

/-! Pieces 78..83 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C013

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (215955, 220014, 6305721325364019, 7954407071847289),
  (220014, 224087, 5570729412510921, 7226505128615892),
  (224087, 228138, 4850441227872312, 6488509149613000),
  (228138, 232222, 4116471398387793, 5769159263375920),
  (232222, 236313, 3393316080505262, 5043123144140004),
  (236313, 240399, 2682124512565470, 4318916964779042)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (215955, 220014, 6305721325364019, 7954407071847289) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (220014, 224087, 5570729412510921, 7226505128615892) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (224087, 228138, 4850441227872312, 6488509149613000) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (228138, 232222, 4116471398387793, 5769159263375920) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (232222, 236313, 3393316080505262, 5043123144140004) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (236313, 240399, 2682124512565470, 4318916964779042) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C013
