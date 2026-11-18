import PINN.Interval

/-! Pieces 180..185 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C030

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (730582, 736963, 3859398266875841, 5512716450831729),
  (736963, 743340, 3829621920174096, 5485478638485100),
  (743340, 749652, 3803409155816157, 5429836723099457),
  (749652, 755973, 3746621808611813, 5381349903064599),
  (755973, 762338, 3669733957718649, 5329753925110764),
  (762338, 768644, 3608706647767974, 5240830941741314)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (730582, 736963, 3859398266875841, 5512716450831729) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (736963, 743340, 3829621920174096, 5485478638485100) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (743340, 749652, 3803409155816157, 5429836723099457) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (749652, 755973, 3746621808611813, 5381349903064599) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (755973, 762338, 3669733957718649, 5329753925110764) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (762338, 768644, 3608706647767974, 5240830941741314) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C030
