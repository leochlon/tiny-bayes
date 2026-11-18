import PINN.Interval

/-! Pieces 42..47 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C007

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (71424, 74322, 7279819073311032, 8921509710215619),
  (74322, 77357, 8419194084585981, 10076302577141818),
  (77357, 80489, 9533850974445977, 11170923649983523),
  (80489, 83773, 10584118769701987, 12234523612828038),
  (83773, 87211, 11590459488582496, 13248455848464297),
  (87211, 87381, 12897991287115818, 12945809565233379)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (71424, 74322, 7279819073311032, 8921509710215619) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (74322, 77357, 8419194084585981, 10076302577141818) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (77357, 80489, 9533850974445977, 11170923649983523) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (80489, 83773, 10584118769701987, 12234523612828038) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (83773, 87211, 11590459488582496, 13248455848464297) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (87211, 87381, 12897991287115818, 12945809565233379) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C007
