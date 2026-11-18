import PINN.Interval

/-! Pieces 330..335 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C055

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2110720, 2117504, 1932556633192419, 3942400790756719),
  (2117504, 2124288, 2077068149241864, 4085976974884206),
  (2124288, 2131053, 2225810825646003, 4223149494916388),
  (2131053, 2137842, 2361594612268562, 4371444457942466),
  (2137842, 2144590, 2514864844633725, 4499752951935070),
  (2144590, 2151377, 2643852824278867, 4649881581636686)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2110720, 2117504, 1932556633192419, 3942400790756719) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2117504, 2124288, 2077068149241864, 4085976974884206) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2124288, 2131053, 2225810825646003, 4223149494916388) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2131053, 2137842, 2361594612268562, 4371444457942466) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2137842, 2144590, 2514864844633725, 4499752951935070) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2144590, 2151377, 2643852824278867, 4649881581636686) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C055
