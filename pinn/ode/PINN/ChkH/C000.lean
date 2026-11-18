import PINN.Interval

/-! Pieces 0..5 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C000

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (0, 4736, -4362731429635235, -2371020678808198),
  (4736, 9600, -3517088875728533, -1502008640607604),
  (9600, 14528, -2693883488991889, -697663850625362),
  (14528, 19584, -1936092251609630, 82805640369941),
  (19584, 24704, -1203096287058418, 796907234183631),
  (24704, 29906, -525421769419572, 1467853273575970)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (0, 4736, -4362731429635235, -2371020678808198) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4736, 9600, -3517088875728533, -1502008640607604) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (9600, 14528, -2693883488991889, -697663850625362) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (14528, 19584, -1936092251609630, 82805640369941) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (19584, 24704, -1203096287058418, 796907234183631) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (24704, 29906, -525421769419572, 1467853273575970) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C000
