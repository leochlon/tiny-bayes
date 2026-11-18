import PINN.Interval

/-! Pieces 510..515 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C085

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3320490, 3327338, -4256756894560358, -2239715367365052),
  (3327338, 3334186, -4169051184634449, -2144979536977808),
  (3334186, 3340970, -4057878999058936, -2063724573218267),
  (3340970, 3347754, -3960168236906781, -1959243749309736),
  (3347754, 3354564, -3864455208714431, -1841786997983914),
  (3354564, 3361332, -3743969111153636, -1738854646467405)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3320490, 3327338, -4256756894560358, -2239715367365052) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3327338, 3334186, -4169051184634449, -2144979536977808) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3334186, 3340970, -4057878999058936, -2063724573218267) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3340970, 3347754, -3960168236906781, -1959243749309736) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3347754, 3354564, -3864455208714431, -1841786997983914) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3354564, 3361332, -3743969111153636, -1738854646467405) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C085
