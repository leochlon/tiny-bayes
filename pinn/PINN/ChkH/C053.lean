import PINN.Interval

/-! Pieces 318..323 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C053

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2030122, 2036906, 191377882615305, 2202888834828788),
  (2036906, 2043671, 342383826656789, 2343847795110028),
  (2043671, 2050461, 481656261724855, 2497543575147780),
  (2050461, 2057209, 640090629970404, 2632297583592728),
  (2057209, 2063996, 775472037926469, 2790393075178440),
  (2063996, 2070795, 919410598808937, 2941245888463783)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2030122, 2036906, 191377882615305, 2202888834828788) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2036906, 2043671, 342383826656789, 2343847795110028) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2043671, 2050461, 481656261724855, 2497543575147780) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2050461, 2057209, 640090629970404, 2632297583592728) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2057209, 2063996, 775472037926469, 2790393075178440) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2063996, 2070795, 919410598808937, 2941245888463783) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C053
