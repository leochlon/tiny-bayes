import PINN.Interval

/-! Pieces 66..71 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C011

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (374805, 381172, -4768614752053590, -2762094206740811),
  (381172, 387594, -4884982928157751, -2858780955315038),
  (387594, 393950, -4953068408095286, -2980867144069173),
  (393950, 400410, -5061895978978704, -3040015462040753),
  (400410, 406895, -5135991143935911, -3112487923458637),
  (406895, 413401, -5197176896557330, -3175190178468997)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (374805, 381172, -4768614752053590, -2762094206740811) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (381172, 387594, -4884982928157751, -2858780955315038) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (387594, 393950, -4953068408095286, -2980867144069173) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (393950, 400410, -5061895978978704, -3040015462040753) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (400410, 406895, -5135991143935911, -3112487923458637) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (406895, 413401, -5197176896557330, -3175190178468997) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C011
