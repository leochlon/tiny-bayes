import PINN.Interval

/-! Pieces 468..473 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C078

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3617450, 3634903, -5688977570209987, -4032023871915582),
  (3634903, 3652322, -5480912023156932, -3821043910858757),
  (3652322, 3669601, -5242399115751673, -3598001373932497),
  (3669601, 3670016, -4297336947184753, -4290406169905951),
  (3670016, 3687168, -4978556925174527, -3346692933661646),
  (3687168, 3704320, -4710442621198545, -3068618125894453)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3617450, 3634903, -5688977570209987, -4032023871915582) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3634903, 3652322, -5480912023156932, -3821043910858757) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3652322, 3669601, -5242399115751673, -3598001373932497) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3669601, 3670016, -4297336947184753, -4290406169905951) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3670016, 3687168, -4978556925174527, -3346692933661646) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3687168, 3704320, -4710442621198545, -3068618125894453) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C078
