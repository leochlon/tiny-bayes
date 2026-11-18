import PINN.Interval

/-! Pieces 12..17 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C002

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (63102, 68934, 2868942193291095, 4868054516147676),
  (68934, 74843, 3166254300964414, 5162670207450615),
  (74843, 80867, 3406252444287611, 5424644099042135),
  (80867, 86973, 3611479484985166, 5632820719478492),
  (86973, 87381, 4704580332065406, 4723584399135477),
  (87381, 93525, 3795985737315523, 5791437920354870)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (63102, 68934, 2868942193291095, 4868054516147676) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (68934, 74843, 3166254300964414, 5162670207450615) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (74843, 80867, 3406252444287611, 5424644099042135) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (80867, 86973, 3611479484985166, 5632820719478492) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (86973, 87381, 4704580332065406, 4723584399135477) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (87381, 93525, 3795985737315523, 5791437920354870) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C002
