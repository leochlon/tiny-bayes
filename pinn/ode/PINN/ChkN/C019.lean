import PINN.Interval

/-! Pieces 114..119 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C019

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (376405, 381958, -10780856882872616, -9153513131930869),
  (381958, 387592, -10802616103071725, -9150094419208514),
  (387592, 393178, -10777954757684851, -9123725484966530),
  (393178, 398644, -10699111531063509, -9087114809757282),
  (398644, 404098, -10620903188526116, -8990507729456455),
  (404098, 409544, -10514499382098264, -8865027738461518)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (376405, 381958, -10780856882872616, -9153513131930869) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (381958, 387592, -10802616103071725, -9150094419208514) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (387592, 393178, -10777954757684851, -9123725484966530) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (393178, 398644, -10699111531063509, -9087114809757282) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (398644, 404098, -10620903188526116, -8990507729456455) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (404098, 409544, -10514499382098264, -8865027738461518) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C019
