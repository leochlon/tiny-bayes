import PINN.Interval

/-! Pieces 456..461 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C076

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2958203, 2964982, -1903400292470849, 84033421917056),
  (2964982, 2970965, -1823217029016496, -262543224567482),
  (2970965, 2977813, -2185222785721563, -164775383188896),
  (2977813, 2984661, -2322456468048381, -305361586813355),
  (2984661, 2991509, -2457327769776922, -443724074809105),
  (2991509, 2998357, -2589702709253827, -579751962122705)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2958203, 2964982, -1903400292470849, 84033421917056) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2964982, 2970965, -1823217029016496, -262543224567482) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2970965, 2977813, -2185222785721563, -164775383188896) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2977813, 2984661, -2322456468048381, -305361586813355) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2984661, 2991509, -2457327769776922, -443724074809105) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2991509, 2998357, -2589702709253827, -579751962122705) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C076
