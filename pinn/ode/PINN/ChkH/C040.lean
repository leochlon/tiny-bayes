import PINN.Interval

/-! Pieces 240..245 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C040

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1506026, 1512874, -3021531602560458, -1013275755125101),
  (1512874, 1519727, -3124652419252824, -1117018480357090),
  (1519727, 1526577, -3221652683921058, -1219859688800323),
  (1526577, 1533447, -3321813989346638, -1312516487506937),
  (1533447, 1540299, -3407421713907111, -1412358489251676),
  (1540299, 1547168, -3499331574867324, -1498344451077110)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1506026, 1512874, -3021531602560458, -1013275755125101) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1512874, 1519727, -3124652419252824, -1117018480357090) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1519727, 1526577, -3221652683921058, -1219859688800323) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1526577, 1533447, -3321813989346638, -1312516487506937) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1533447, 1540299, -3407421713907111, -1412358489251676) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1540299, 1547168, -3499331574867324, -1498344451077110) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C040
