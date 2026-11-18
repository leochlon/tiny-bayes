import PINN.Interval

/-! Pieces 48..53 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C008

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (87381, 90965, 12591701065272634, 14240292111147150),
  (90965, 94709, 13475048539400017, 15122168118474996),
  (94709, 98645, 14281847771138137, 15941462944822241),
  (98645, 102741, 15022449979823114, 16667562986327207),
  (102741, 107029, 15666550809306471, 17311885398692182),
  (107029, 111509, 16217390442932764, 17857447769019978)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (87381, 90965, 12591701065272634, 14240292111147150) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (90965, 94709, 13475048539400017, 15122168118474996) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (94709, 98645, 14281847771138137, 15941462944822241) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (98645, 102741, 15022449979823114, 16667562986327207) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (102741, 107029, 15666550809306471, 17311885398692182) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (107029, 111509, 16217390442932764, 17857447769019978) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C008
