import PINN.Interval

/-! Pieces 348..353 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C058

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2232106, 2238948, 4291393327226216, 6310510132807514),
  (2238948, 2245772, 4411623981650295, 6418252624807433),
  (2245772, 2252614, 4518932297573276, 6533655518189496),
  (2252614, 2259473, 4623963828358406, 6646422621279802),
  (2259473, 2266276, 4746968473005712, 6735003853202939),
  (2266276, 2271914, 5145826050353384, 6523839714267511)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2232106, 2238948, 4291393327226216, 6310510132807514) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2238948, 2245772, 4411623981650295, 6418252624807433) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2245772, 2252614, 4518932297573276, 6533655518189496) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2252614, 2259473, 4623963828358406, 6646422621279802) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2259473, 2266276, 4746968473005712, 6735003853202939) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2266276, 2271914, 5145826050353384, 6523839714267511) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C058
