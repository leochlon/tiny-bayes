import PINN.Interval

/-! Pieces 216..221 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C036

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (959051, 961194, -260839393264569, -60345822997733),
  (961194, 967914, -1077251337568169, 555534623809226),
  (967914, 974698, -1234232410384221, 414508873694854),
  (974698, 981482, -1372150942859739, 262513907372117),
  (981482, 988330, -1520344630785587, 129422787681365),
  (988330, 995213, -1657520335034768, -6212599834654)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (959051, 961194, -260839393264569, -60345822997733) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (961194, 967914, -1077251337568169, 555534623809226) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (967914, 974698, -1234232410384221, 414508873694854) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (974698, 981482, -1372150942859739, 262513907372117) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (981482, 988330, -1520344630785587, 129422787681365) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (988330, 995213, -1657520335034768, -6212599834654) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C036
