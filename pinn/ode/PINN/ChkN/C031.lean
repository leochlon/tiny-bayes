import PINN.Interval

/-! Pieces 186..191 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C031

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (768644, 774966, 3518923337407053, 5160869619575736),
  (774966, 781236, 3437259509183872, 5054246109600695),
  (781236, 786432, 3589234356202462, 4715284317002276),
  (786432, 792768, 3225869827751125, 4876578373417585),
  (792768, 799104, 3107545564936954, 4757729691934214),
  (799104, 805440, 2982174790081415, 4631249479151152)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (768644, 774966, 3518923337407053, 5160869619575736) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (774966, 781236, 3437259509183872, 5054246109600695) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (781236, 786432, 3589234356202462, 4715284317002276) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (786432, 792768, 3225869827751125, 4876578373417585) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (792768, 799104, 3107545564936954, 4757729691934214) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (799104, 805440, 2982174790081415, 4631249479151152) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C031
