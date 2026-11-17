import PINN.Interval

/-! Pieces 312..317 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C052

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1990532, 1997295, -639462788759688, 1354797086245016),
  (1997295, 2004117, -515013040567125, 1513932904734576),
  (2004117, 2009770, -76671931206893, 1337827513778409),
  (2009770, 2016554, -242469477967264, 1766699390063795),
  (2016554, 2023338, -98617029600732, 1911454357277419),
  (2023338, 2030122, 46034354149621, 2056887943402882)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1990532, 1997295, -639462788759688, 1354797086245016) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1997295, 2004117, -515013040567125, 1513932904734576) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2004117, 2009770, -76671931206893, 1337827513778409) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2009770, 2016554, -242469477967264, 1766699390063795) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2016554, 2023338, -98617029600732, 1911454357277419) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2023338, 2030122, 46034354149621, 2056887943402882) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C052
