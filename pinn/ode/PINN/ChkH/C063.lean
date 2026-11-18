import PINN.Interval

/-! Pieces 378..383 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C063

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2435759, 2442752, 6289351787400597, 8296528718211167),
  (2442752, 2446677, 6983458856234896, 7616640758497177),
  (2446677, 2453717, 6291031877560153, 8318071211874651),
  (2453717, 2460757, 6295140982435232, 8317731066520192),
  (2460757, 2467797, 6291425198585948, 8316462314813297),
  (2467797, 2474773, 6300775968383606, 8293440074481627)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2435759, 2442752, 6289351787400597, 8296528718211167) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2442752, 2446677, 6983458856234896, 7616640758497177) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2446677, 2453717, 6291031877560153, 8318071211874651) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2453717, 2460757, 6295140982435232, 8317731066520192) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2460757, 2467797, 6291425198585948, 8316462314813297) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2467797, 2474773, 6300775968383606, 8293440074481627) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C063
