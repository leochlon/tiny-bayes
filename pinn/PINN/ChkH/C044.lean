import PINN.Interval

/-! Pieces 264..269 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C044

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1667285, 1674325, -4411432755534246, -2396283294100138),
  (1674325, 1681365, -4415890792998232, -2405568522784633),
  (1681365, 1688405, -4415981091895350, -2409977369622106),
  (1688405, 1695460, -4420238518232514, -2400982929001911),
  (1695460, 1702490, -4408186635704362, -2399101362250914),
  (1702490, 1709542, -4405093230751545, -2379091112676819)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1667285, 1674325, -4411432755534246, -2396283294100138) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1674325, 1681365, -4415890792998232, -2405568522784633) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1681365, 1688405, -4415981091895350, -2409977369622106) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1688405, 1695460, -4420238518232514, -2400982929001911) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1695460, 1702490, -4408186635704362, -2399101362250914) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1702490, 1709542, -4405093230751545, -2379091112676819) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C044
