import PINN.Interval

/-! Pieces 456..461 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C076

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3407872, 3425024, -6555391378242883, -4935482106533644),
  (3425024, 3442432, -6594742036072663, -4960190793987847),
  (3442432, 3459970, -6604457508666333, -4980156013759006),
  (3459970, 3477612, -6607816188909674, -4969946179111645),
  (3477612, 3495253, -6586622543186216, -4946202215269454),
  (3495253, 3512917, -6548272782110700, -4900404668572605)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3407872, 3425024, -6555391378242883, -4935482106533644) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3425024, 3442432, -6594742036072663, -4960190793987847) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3442432, 3459970, -6604457508666333, -4980156013759006) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3459970, 3477612, -6607816188909674, -4969946179111645) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3477612, 3495253, -6586622543186216, -4946202215269454) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3495253, 3512917, -6548272782110700, -4900404668572605) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C076
