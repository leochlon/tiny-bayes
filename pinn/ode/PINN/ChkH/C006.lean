import PINN.Interval

/-! Pieces 36..41 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C006

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (198890, 204881, 1620511135241392, 3613026194456734),
  (204881, 210920, 1343465581862066, 3369009306728134),
  (210920, 216922, 1089233082950108, 3093180685463001),
  (216922, 222928, 820252908609030, 2827420833345147),
  (222928, 228901, 561810472731168, 2548463754826908),
  (228901, 234939, 271955755523198, 2297407238739097)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (198890, 204881, 1620511135241392, 3613026194456734) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (204881, 210920, 1343465581862066, 3369009306728134) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (210920, 216922, 1089233082950108, 3093180685463001) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (216922, 222928, 820252908609030, 2827420833345147) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (222928, 228901, 561810472731168, 2548463754826908) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (228901, 234939, 271955755523198, 2297407238739097) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C006
