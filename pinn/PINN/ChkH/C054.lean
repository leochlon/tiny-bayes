import PINN.Interval

/-! Pieces 324..329 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C054

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2070795, 2077590, 1068063658249580, 3087493646542813),
  (2077590, 2084390, 1214210904625286, 3236025261204623),
  (2084390, 2091169, 1367131279213468, 3376905566130587),
  (2091169, 2097152, 1719633353856613, 3299899028807113),
  (2097152, 2103936, 1641511544423617, 3652849506854592),
  (2103936, 2110720, 1787336807406099, 3797989825678936)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2070795, 2077590, 1068063658249580, 3087493646542813) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2077590, 2084390, 1214210904625286, 3236025261204623) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2084390, 2091169, 1367131279213468, 3376905566130587) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2091169, 2097152, 1719633353856613, 3299899028807113) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2097152, 2103936, 1641511544423617, 3652849506854592) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2103936, 2110720, 1787336807406099, 3797989825678936) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C054
