import PINN.Interval

/-! Pieces 276..281 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C046

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1747626, 1754602, -4215940962828291, -2206225955725848),
  (1754602, 1761578, -4173760315945023, -2160023566838033),
  (1761578, 1768554, -4127330559124647, -2109623579145583),
  (1768554, 1775530, -4076706765445561, -2055081090006533),
  (1775530, 1782500, -4020255880647563, -1998156309228163),
  (1782500, 1789474, -3962633309747542, -1934299053964763)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1747626, 1754602, -4215940962828291, -2206225955725848) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1754602, 1761578, -4173760315945023, -2160023566838033) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1761578, 1768554, -4127330559124647, -2109623579145583) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1768554, 1775530, -4076706765445561, -2055081090006533) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1775530, 1782500, -4020255880647563, -1998156309228163) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1782500, 1789474, -3962633309747542, -1934299053964763) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C046
