import PINN.Interval

/-! Pieces 342..347 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C057

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2008537, 2009770, 1033553354196399, 1060473490859387),
  (2009770, 2020650, 261327418201293, 1897233647690483),
  (2020650, 2031530, 325276313192205, 1951581963070801),
  (2031530, 2042538, 372271504059371, 2026498106747490),
  (2042538, 2053524, 443074381347507, 2080937976752364),
  (2053524, 2064601, 498755493383110, 2153420558073894)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2008537, 2009770, 1033553354196399, 1060473490859387) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2009770, 2020650, 261327418201293, 1897233647690483) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2020650, 2031530, 325276313192205, 1951581963070801) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2031530, 2042538, 372271504059371, 2026498106747490) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2042538, 2053524, 443074381347507, 2080937976752364) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2053524, 2064601, 498755493383110, 2153420558073894) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C057
