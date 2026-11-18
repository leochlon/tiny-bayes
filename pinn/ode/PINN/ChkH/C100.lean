import PINN.Interval

/-! Pieces 600..605 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C100

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3899103, 3905818, 8457708294974590, 10484260836567119),
  (3905818, 3912506, 8350545414516503, 10378131405965530),
  (3912506, 3919108, 8245083280753585, 10239571868283611),
  (3919108, 3925735, 8090801603272241, 10117895177450387),
  (3925735, 3932160, 7988054665517193, 9915116113667722),
  (3932160, 3938688, 7781078467535821, 9785344623346506)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3899103, 3905818, 8457708294974590, 10484260836567119) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3905818, 3912506, 8350545414516503, 10378131405965530) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3912506, 3919108, 8245083280753585, 10239571868283611) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3919108, 3925735, 8090801603272241, 10117895177450387) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3925735, 3932160, 7988054665517193, 9915116113667722) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3932160, 3938688, 7781078467535821, 9785344623346506) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C100
