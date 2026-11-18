import PINN.Interval

/-! Pieces 546..551 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C091

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3554339, 3560859, 1490961416378118, 3491570723490939),
  (3560859, 3567408, 1696687636475383, 3716434635246871),
  (3567408, 3573950, 1914809935404642, 3931934876246502),
  (3573950, 3580463, 2139446157480420, 4141511075855400),
  (3580463, 3582634, 3149702715892673, 3420932532777383),
  (3582634, 3589162, 2424594910494445, 4436770284007587)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3554339, 3560859, 1490961416378118, 3491570723490939) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3560859, 3567408, 1696687636475383, 3716434635246871) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3567408, 3573950, 1914809935404642, 3931934876246502) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3573950, 3580463, 2139446157480420, 4141511075855400) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3580463, 3582634, 3149702715892673, 3420932532777383) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3582634, 3589162, 2424594910494445, 4436770284007587) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C091
