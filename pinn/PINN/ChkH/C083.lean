import PINN.Interval

/-! Pieces 498..503 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C083

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3240085, 3247061, -4907352951990727, -2902476312595315),
  (3247061, 3254037, -4884399019625283, -2871937743361890),
  (3254037, 3261013, -4855719561495754, -2835677946871528),
  (3261013, 3267983, -4819579104077175, -2795415278140551),
  (3267983, 3274854, -4751550272331883, -2776240891431552),
  (3274854, 3281806, -4729060122154156, -2700285499908269)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3240085, 3247061, -4907352951990727, -2902476312595315) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3247061, 3254037, -4884399019625283, -2871937743361890) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3254037, 3261013, -4855719561495754, -2835677946871528) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3261013, 3267983, -4819579104077175, -2795415278140551) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3267983, 3274854, -4751550272331883, -2776240891431552) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3274854, 3281806, -4729060122154156, -2700285499908269) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C083
