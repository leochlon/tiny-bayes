import PINN.Interval

/-! Pieces 504..509 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C084

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3281806, 3288680, -4655491706534778, -2664055176150479),
  (3288680, 3295576, -4605120868761444, -2593788816799256),
  (3295576, 3302485, -4546570595320423, -2520106459479034),
  (3302485, 3309377, -4473423357075598, -2449763637019456),
  (3309377, 3316236, -4390600271768332, -2378440395490505),
  (3316236, 3320490, -3716152970187856, -2920148767356546)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3281806, 3288680, -4655491706534778, -2664055176150479) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3288680, 3295576, -4605120868761444, -2593788816799256) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3295576, 3302485, -4546570595320423, -2520106459479034) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3302485, 3309377, -4473423357075598, -2449763637019456) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3309377, 3316236, -4390600271768332, -2378440395490505) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3316236, 3320490, -3716152970187856, -2920148767356546) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C084
