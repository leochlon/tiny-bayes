import PINN.Interval

/-! Pieces 492..497 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C082

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3201738, 3208783, -4958400790934989, -2943530296866488),
  (3208783, 3215815, -4956917318814049, -2953370887155539),
  (3215815, 3222840, -4957103704473231, -2950280467052842),
  (3222840, 3229819, -4940712109676642, -2952501687292293),
  (3229819, 3233109, -4161121364875001, -3714494340528447),
  (3233109, 3240085, -4924611525924912, -2927292801212849)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3201738, 3208783, -4958400790934989, -2943530296866488) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3208783, 3215815, -4956917318814049, -2953370887155539) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3215815, 3222840, -4957103704473231, -2950280467052842) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3222840, 3229819, -4940712109676642, -2952501687292293) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3229819, 3233109, -4161121364875001, -3714494340528447) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3233109, 3240085, -4924611525924912, -2927292801212849) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C082
