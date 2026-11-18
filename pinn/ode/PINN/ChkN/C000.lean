import PINN.Interval

/-! Pieces 0..5 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C000

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (0, 1120, -54293693269629837, -52645447584618299),
  (1120, 2256, -52719405645136015, -51070091316299045),
  (2256, 3408, -51146133346568197, -49496526193039739),
  (3408, 4576, -49574679077467588, -47925548240091428),
  (4576, 5760, -48005840353481051, -46357953909300928),
  (5760, 6960, -46440411641821262, -44794536525314472)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (0, 1120, -54293693269629837, -52645447584618299) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (1120, 2256, -52719405645136015, -51070091316299045) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2256, 3408, -51146133346568197, -49496526193039739) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3408, 4576, -49574679077467588, -47925548240091428) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (4576, 5760, -48005840353481051, -46357953909300928) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (5760, 6960, -46440411641821262, -44794536525314472) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C000
