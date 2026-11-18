import PINN.Interval

/-! Pieces 390..395 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C065

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2534058, 2547114, 2276280752147567, 3936336593792238),
  (2547114, 2560170, 2243255878970951, 3896487354035153),
  (2560170, 2573213, 2205351388831779, 3848771450012168),
  (2573213, 2586211, 2165134414089620, 3790768787828509),
  (2586211, 2599284, 2103527603797526, 3741250930031993),
  (2599284, 2612438, 2034564541777133, 3685509655188227)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2534058, 2547114, 2276280752147567, 3936336593792238) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2547114, 2560170, 2243255878970951, 3896487354035153) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2560170, 2573213, 2205351388831779, 3848771450012168) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2573213, 2586211, 2165134414089620, 3790768787828509) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2586211, 2599284, 2103527603797526, 3741250930031993) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2599284, 2612438, 2034564541777133, 3685509655188227) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C065
