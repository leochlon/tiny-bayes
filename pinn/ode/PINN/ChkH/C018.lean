import PINN.Interval

/-! Pieces 108..113 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C018

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (637269, 643663, -1553148707025600, 459785452900164),
  (643663, 650045, -1351624804837941, 653463915418094),
  (650045, 656457, -1160866214447687, 861223572087338),
  (656457, 662863, -957726879673874, 1059526554244025),
  (662863, 669223, -742563520179766, 1245785070329897),
  (669223, 675631, -554718585076190, 1460462927464772)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (637269, 643663, -1553148707025600, 459785452900164) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (643663, 650045, -1351624804837941, 653463915418094) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (650045, 656457, -1160866214447687, 861223572087338) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (656457, 662863, -957726879673874, 1059526554244025) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (662863, 669223, -742563520179766, 1245785070329897) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (669223, 675631, -554718585076190, 1460462927464772) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C018
