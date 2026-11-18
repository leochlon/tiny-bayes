import PINN.Interval

/-! Pieces 126..131 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C021

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (750565, 757009, 1955773256894330, 3948776722674557),
  (757009, 763502, 2129033062742722, 4146369716500311),
  (763502, 769951, 2327083937359648, 4313301266845042),
  (769951, 776453, 2493690530867486, 4505532772544428),
  (776453, 782923, 2682164745516727, 4669630233800925),
  (782923, 786432, 3496028172671216, 4122092205412145)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (750565, 757009, 1955773256894330, 3948776722674557) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (757009, 763502, 2129033062742722, 4146369716500311) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (763502, 769951, 2327083937359648, 4313301266845042) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (769951, 776453, 2493690530867486, 4505532772544428) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (776453, 782923, 2682164745516727, 4669630233800925) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (782923, 786432, 3496028172671216, 4122092205412145) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C021
