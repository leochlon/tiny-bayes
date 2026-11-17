import PINN.Interval

/-! Pieces 162..167 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C027

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (622997, 628693, 2007443637699196, 3645947317579865),
  (628693, 634453, 2221091298755805, 3874154107899220),
  (634453, 640256, 2428336017757374, 4084415544311357),
  (640256, 646054, 2635126929000974, 4267668435673942),
  (646054, 651902, 2813424879638903, 4451673267484448),
  (651902, 657796, 2979668341967848, 4621064684774262)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (622997, 628693, 2007443637699196, 3645947317579865) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (628693, 634453, 2221091298755805, 3874154107899220) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (634453, 640256, 2428336017757374, 4084415544311357) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (640256, 646054, 2635126929000974, 4267668435673942) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (646054, 651902, 2813424879638903, 4451673267484448) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (651902, 657796, 2979668341967848, 4621064684774262) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C027
