import PINN.Interval

/-! Pieces 570..575 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C095

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3702709, 3709277, 6276023498382828, 8290379929586480),
  (3709277, 3715855, 6460208181641918, 8476828191787750),
  (3715855, 3722427, 6644716596512854, 8653904219749181),
  (3722427, 3728984, 6826673029257805, 8823179327254610),
  (3728984, 3735588, 6986253687062608, 9005309853417017),
  (3735588, 3742148, 7166918841369646, 9155344700125372)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3702709, 3709277, 6276023498382828, 8290379929586480) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3709277, 3715855, 6460208181641918, 8476828191787750) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3715855, 3722427, 6644716596512854, 8653904219749181) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3722427, 3728984, 6826673029257805, 8823179327254610) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3728984, 3735588, 6986253687062608, 9005309853417017) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3735588, 3742148, 7166918841369646, 9155344700125372) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C095
