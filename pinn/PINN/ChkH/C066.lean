import PINN.Interval

/-! Pieces 396..401 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C066

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2554794, 2561706, 5850607169436906, 7858086173049347),
  (2561706, 2568647, 5777064760138231, 7805504341266405),
  (2568647, 2575556, 5717232715311470, 7731339880092406),
  (2575556, 2582455, 5647463663932710, 7659763879418794),
  (2582455, 2589308, 5584504134523938, 7574346687511706),
  (2589308, 2596211, 5490382029411499, 7512554932759004)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2554794, 2561706, 5850607169436906, 7858086173049347) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2561706, 2568647, 5777064760138231, 7805504341266405) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2568647, 2575556, 5717232715311470, 7731339880092406) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2575556, 2582455, 5647463663932710, 7659763879418794) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2582455, 2589308, 5584504134523938, 7574346687511706) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2589308, 2596211, 5490382029411499, 7512554932759004) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C066
