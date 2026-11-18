import PINN.Interval

/-! Pieces 468..473 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C078

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3039475, 3046330, -3440832889731411, -1453108758548464),
  (3046330, 3053182, -3548816547081187, -1566518482272961),
  (3053182, 3058346, -3223902767282505, -2079808776072617),
  (3058346, 3065258, -3748649082987359, -1738869421717089),
  (3065258, 3072170, -3848448576378053, -1842516956197338),
  (3072170, 3079082, -3944359873431539, -1942410432486616)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3039475, 3046330, -3440832889731411, -1453108758548464) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3046330, 3053182, -3548816547081187, -1566518482272961) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3053182, 3058346, -3223902767282505, -2079808776072617) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3058346, 3065258, -3748649082987359, -1738869421717089) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3065258, 3072170, -3848448576378053, -1842516956197338) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3072170, 3079082, -3944359873431539, -1942410432486616) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C078
