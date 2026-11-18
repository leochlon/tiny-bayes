import PINN.Interval

/-! Pieces 288..293 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C048

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1830896, 1835008, -2805874217806754, -2070378364597684),
  (1835008, 1841920, -3377741278407697, -1356769259247226),
  (1841920, 1848832, -3287479966053799, -1263156495512693),
  (1848832, 1855744, -3193832837125845, -1166239297044833),
  (1855744, 1862592, -3079091594850684, -1084821261877432),
  (1862592, 1869482, -2991733489980204, -970060566191383)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1830896, 1835008, -2805874217806754, -2070378364597684) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1835008, 1841920, -3377741278407697, -1356769259247226) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1841920, 1848832, -3287479966053799, -1263156495512693) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1848832, 1855744, -3193832837125845, -1166239297044833) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1855744, 1862592, -3079091594850684, -1084821261877432) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1862592, 1869482, -2991733489980204, -970060566191383) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C048
