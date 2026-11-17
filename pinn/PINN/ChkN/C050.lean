import PINN.Interval

/-! Pieces 300..305 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C050

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1600768, 1610177, -912019602006323, 739229155597620),
  (1610177, 1619565, -878143693534644, 750320904220675),
  (1619565, 1629019, -860607959416845, 775349905685043),
  (1629019, 1638533, -842975295944306, 798270252522365),
  (1638533, 1648116, -827804829618837, 821849693491993),
  (1648116, 1657686, -799331137564092, 830405744905491)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (1600768, 1610177, -912019602006323, 739229155597620) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1610177, 1619565, -878143693534644, 750320904220675) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (1619565, 1629019, -860607959416845, 775349905685043) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (1629019, 1638533, -842975295944306, 798270252522365) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (1638533, 1648116, -827804829618837, 821849693491993) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (1648116, 1657686, -799331137564092, 830405744905491) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C050
