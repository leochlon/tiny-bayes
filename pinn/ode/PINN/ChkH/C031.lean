import PINN.Interval

/-! Pieces 186..191 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C031

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1142741, 1149525, 4496262171870992, 6507769994145372),
  (1149525, 1156309, 4382821965543480, 6396933674746538),
  (1156309, 1163093, 4265796471991170, 6282411503314237),
  (1163093, 1169858, 4150828784633341, 6159203296541446),
  (1169858, 1176647, 4020284730696787, 6044782111388817),
  (1176647, 1183395, 3905637850764934, 5908373141337245)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1142741, 1149525, 4496262171870992, 6507769994145372) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1149525, 1156309, 4382821965543480, 6396933674746538) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1156309, 1163093, 4265796471991170, 6282411503314237) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1163093, 1169858, 4150828784633341, 6159203296541446) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1169858, 1176647, 4020284730696787, 6044782111388817) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1176647, 1183395, 3905637850764934, 5908373141337245) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C031
