import PINN.Interval

/-! Pieces 498..503 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C083

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4051157, 4066841, 6447525132411515, 8091466034281921),
  (4066841, 4082498, 7153936808418661, 8805026224450337),
  (4082498, 4097953, 7887574812781048, 9516712815661517),
  (4097953, 4106922, 8915848659030680, 9647759398663654),
  (4106922, 4122410, 9047128903174199, 10698989505922141),
  (4122410, 4137770, 9813224390602401, 11454862944769750)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (4051157, 4066841, 6447525132411515, 8091466034281921) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (4066841, 4082498, 7153936808418661, 8805026224450337) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (4082498, 4097953, 7887574812781048, 9516712815661517) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (4097953, 4106922, 8915848659030680, 9647759398663654) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (4106922, 4122410, 9047128903174199, 10698989505922141) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (4122410, 4137770, 9813224390602401, 11454862944769750) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C083
