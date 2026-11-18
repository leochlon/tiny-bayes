import PINN.Interval

/-! Pieces 366..371 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C061

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2265971, 2271914, 2377786944576929, 2809814702949339),
  (2271914, 2283818, 1810771266919448, 3470522542420008),
  (2283818, 2295722, 1878377319265955, 3523697741516215),
  (2295722, 2307642, 1941342792909327, 3576420470494728),
  (2307642, 2319647, 1992525542600739, 3635793351605361),
  (2319647, 2331728, 2042532018310668, 3691002497952584)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2265971, 2271914, 2377786944576929, 2809814702949339) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2271914, 2283818, 1810771266919448, 3470522542420008) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2283818, 2295722, 1878377319265955, 3523697741516215) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2295722, 2307642, 1941342792909327, 3576420470494728) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2307642, 2319647, 1992525542600739, 3635793351605361) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2319647, 2331728, 2042532018310668, 3691002497952584) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C061
