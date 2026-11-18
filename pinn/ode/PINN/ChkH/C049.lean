import PINN.Interval

/-! Pieces 294..299 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C049

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1869482, 1876302, -2869565079828926, -884428812846210),
  (1876302, 1883143, -2770828103598373, -770248152111613),
  (1883143, 1889964, -2657372149163448, -665050330987951),
  (1889964, 1896803, -2551939047840813, -546354808706622),
  (1896803, 1903599, -2426487923061637, -442744121031243),
  (1903599, 1910424, -2319312475990626, -315998172159657)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1869482, 1876302, -2869565079828926, -884428812846210) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1876302, 1883143, -2770828103598373, -770248152111613) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1883143, 1889964, -2657372149163448, -665050330987951) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1889964, 1896803, -2551939047840813, -546354808706622) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1896803, 1903599, -2426487923061637, -442744121031243) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1903599, 1910424, -2319312475990626, -315998172159657) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C049
