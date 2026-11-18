import PINN.Interval

/-! Pieces 228..233 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C038

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1425237, 1432002, -1559571402912108, 439274743076597),
  (1432002, 1438791, -1701977436739536, 307934706799537),
  (1438791, 1445539, -1823155529195717, 160373994224307),
  (1445539, 1452326, -1964871307503583, 38331671395502),
  (1452326, 1459125, -2096644740454997, -89524226644072),
  (1459125, 1465920, -2221186900202010, -219391404396991)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1425237, 1432002, -1559571402912108, 439274743076597) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1432002, 1438791, -1701977436739536, 307934706799537) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1438791, 1445539, -1823155529195717, 160373994224307) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1445539, 1452326, -1964871307503583, 38331671395502) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1452326, 1459125, -2096644740454997, -89524226644072) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1459125, 1465920, -2221186900202010, -219391404396991) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C038
