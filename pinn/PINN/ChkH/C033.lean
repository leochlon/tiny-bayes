import PINN.Interval

/-! Pieces 198..203 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C033

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1223338, 1230058, 2967797408056532, 4965634334148962),
  (1230058, 1236778, 2822906992510514, 4821816201675331),
  (1236778, 1243498, 2676264820712191, 4676114451765466),
  (1243498, 1250218, 2528034520230436, 4528683709276849),
  (1250218, 1256953, 2373745441021899, 4383970896208923),
  (1256953, 1263674, 2226616485173829, 4229333083601315)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1223338, 1230058, 2967797408056532, 4965634334148962) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1230058, 1236778, 2822906992510514, 4821816201675331) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1236778, 1243498, 2676264820712191, 4676114451765466) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1243498, 1250218, 2528034520230436, 4528683709276849) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1250218, 1256953, 2373745441021899, 4383970896208923) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1256953, 1263674, 2226616485173829, 4229333083601315) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C033
