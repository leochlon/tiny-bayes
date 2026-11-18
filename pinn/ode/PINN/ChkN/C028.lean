import PINN.Interval

/-! Pieces 168..173 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C028

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (657796, 663758, 3126860133778155, 4782628544116634),
  (663758, 669754, 3269323551793083, 4921067925775656),
  (669754, 675761, 3403028891936073, 5038737190059557),
  (675761, 681856, 3502464711454083, 5162108659588231),
  (681856, 687967, 3606537878407986, 5251996070172901),
  (687967, 694114, 3690502467131168, 5332234652193489)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (657796, 663758, 3126860133778155, 4782628544116634) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (663758, 669754, 3269323551793083, 4921067925775656) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (669754, 675761, 3403028891936073, 5038737190059557) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (675761, 681856, 3502464711454083, 5162108659588231) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (681856, 687967, 3606537878407986, 5251996070172901) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (687967, 694114, 3690502467131168, 5332234652193489) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C028
