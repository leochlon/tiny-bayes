import PINN.Interval

/-! Pieces 138..143 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C023

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (825693, 832271, 3884724138949608, 5888877906574049),
  (832271, 838843, 4032133635530180, 6025956678086706),
  (838843, 845468, 4157661234744926, 6175959145151255),
  (845468, 852112, 4289177935048622, 6311222584155950),
  (852112, 858724, 4430156747740940, 6426226729941492),
  (858724, 865384, 4542512191059595, 6559434293679718)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (825693, 832271, 3884724138949608, 5888877906574049) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (832271, 838843, 4032133635530180, 6025956678086706) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (838843, 845468, 4157661234744926, 6175959145151255) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (845468, 852112, 4289177935048622, 6311222584155950) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (852112, 858724, 4430156747740940, 6426226729941492) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (858724, 865384, 4542512191059595, 6559434293679718) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C023
