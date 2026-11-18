import PINN.Interval

/-! Pieces 174..179 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C029

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (694114, 699050, 4045135433276546, 5100180444847559),
  (699050, 705258, 3805778238583018, 5438485009581366),
  (705258, 711530, 3841729606016015, 5485078028034370),
  (711530, 717866, 3863391711302890, 5517273392771577),
  (717866, 724202, 3887195789951912, 5518580839139987),
  (724202, 730582, 3877639776191437, 5525044873876550)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (694114, 699050, 4045135433276546, 5100180444847559) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (699050, 705258, 3805778238583018, 5438485009581366) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (705258, 711530, 3841729606016015, 5485078028034370) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (711530, 717866, 3863391711302890, 5517273392771577) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (717866, 724202, 3887195789951912, 5518580839139987) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (724202, 730582, 3877639776191437, 5525044873876550) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C029
