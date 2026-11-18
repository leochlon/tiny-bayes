import PINN.Interval

/-! Pieces 462..467 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C077

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3512917, 3530581, -6488079384557541, -4836201783961928),
  (3530581, 3548067, -6392322714167759, -4767371000585084),
  (3548067, 3565621, -6299048362345707, -4655190753741204),
  (3565621, 3582634, -6132526739904817, -4577772997071095),
  (3582634, 3600042, -6029052570477501, -4396873893653612),
  (3600042, 3617450, -5867908409119267, -4227629115848744)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3512917, 3530581, -6488079384557541, -4836201783961928) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3530581, 3548067, -6392322714167759, -4767371000585084) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3548067, 3565621, -6299048362345707, -4655190753741204) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3565621, 3582634, -6132526739904817, -4577772997071095) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3582634, 3600042, -6029052570477501, -4396873893653612) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3600042, 3617450, -5867908409119267, -4227629115848744) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C077
