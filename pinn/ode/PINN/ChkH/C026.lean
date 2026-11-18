import PINN.Interval

/-! Pieces 156..161 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C026

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (941169, 947974, 5598144757261061, 7604543172460871),
  (947974, 954790, 5645031837972904, 7649491389073751),
  (954790, 961194, 5803481135401949, 7568131656826414),
  (961194, 968042, 5714772409786447, 7722246886462725),
  (968042, 974890, 5746365591092678, 7745800377947253),
  (974890, 981802, 5753115881297797, 7781754010368615)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (941169, 947974, 5598144757261061, 7604543172460871) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (947974, 954790, 5645031837972904, 7649491389073751) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (954790, 961194, 5803481135401949, 7568131656826414) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (961194, 968042, 5714772409786447, 7722246886462725) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (968042, 974890, 5746365591092678, 7745800377947253) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (974890, 981802, 5753115881297797, 7781754010368615) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C026
