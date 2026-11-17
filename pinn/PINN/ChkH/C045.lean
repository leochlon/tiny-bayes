import PINN.Interval

/-! Pieces 270..275 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C045

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1709542, 1716534, -4374083931806920, -2377974921397445),
  (1716534, 1723517, -4353327753075630, -2357795077207883),
  (1723517, 1730486, -4326586038136840, -2334806535646280),
  (1730486, 1737448, -4297315058077838, -2305636931938550),
  (1737448, 1744445, -4275849738751824, -2259820954098582),
  (1744445, 1747626, -3454184599362732, -3026956543963732)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1709542, 1716534, -4374083931806920, -2377974921397445) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1716534, 1723517, -4353327753075630, -2357795077207883) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1723517, 1730486, -4326586038136840, -2334806535646280) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1730486, 1737448, -4297315058077838, -2305636931938550) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1737448, 1744445, -4275849738751824, -2259820954098582) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1744445, 1747626, -3454184599362732, -3026956543963732) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C045
