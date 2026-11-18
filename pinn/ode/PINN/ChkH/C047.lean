import PINN.Interval

/-! Pieces 282..287 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C047

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1789474, 1796411, -3889607976065509, -1878158446094772),
  (1796411, 1803346, -3822663608742297, -1808473933924421),
  (1803346, 1810272, -3749750255871708, -1737174471934122),
  (1810272, 1817132, -3657403224646458, -1678622000402946),
  (1817132, 1824044, -3594944716458230, -1583019741388065),
  (1824044, 1830896, -3497099395428499, -1515724276634388)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1789474, 1796411, -3889607976065509, -1878158446094772) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1796411, 1803346, -3822663608742297, -1808473933924421) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1803346, 1810272, -3749750255871708, -1737174471934122) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1810272, 1817132, -3657403224646458, -1678622000402946) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1817132, 1824044, -3594944716458230, -1583019741388065) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1824044, 1830896, -3497099395428499, -1515724276634388) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C047
