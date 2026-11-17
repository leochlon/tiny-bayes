import PINN.Interval

/-! Pieces 96..101 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C016

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (288128, 292625, -5232714771577232, -3585090802246711),
  (292625, 297182, -5779617023278672, -4124929155582372),
  (297182, 301782, -6298996563683595, -4649353979130402),
  (301782, 306444, -6800728689430276, -5145580574197150),
  (306444, 311156, -7274242982716231, -5622186983055686),
  (311156, 315915, -7720400313776050, -6074056820164137)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (288128, 292625, -5232714771577232, -3585090802246711) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (292625, 297182, -5779617023278672, -4124929155582372) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (297182, 301782, -6298996563683595, -4649353979130402) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (301782, 306444, -6800728689430276, -5145580574197150) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (306444, 311156, -7274242982716231, -5622186983055686) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (311156, 315915, -7720400313776050, -6074056820164137) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C016
