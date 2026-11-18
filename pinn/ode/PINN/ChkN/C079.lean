import PINN.Interval

/-! Pieces 474..479 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C079

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3704320, 3721321, -4408313921453326, -2782470419549412),
  (3721321, 3738372, -4102336969636238, -2457339600107934),
  (3738372, 3755316, -3760998940947638, -2123936598944374),
  (3755316, 3757397, -2775704707089476, -2712075762887368),
  (3757397, 3774293, -3359278249270250, -1718264193786604),
  (3774293, 3791189, -2982174895249594, -1330074588625338)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3704320, 3721321, -4408313921453326, -2782470419549412) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3721321, 3738372, -4102336969636238, -2457339600107934) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3738372, 3755316, -3760998940947638, -2123936598944374) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3755316, 3757397, -2775704707089476, -2712075762887368) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3757397, 3774293, -3359278249270250, -1718264193786604) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3774293, 3791189, -2982174895249594, -1330074588625338) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C079
