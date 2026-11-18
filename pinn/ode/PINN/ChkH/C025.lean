import PINN.Interval

/-! Pieces 150..155 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C025

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (900629, 907371, 5189115101719270, 7206232182270911),
  (907371, 914099, 5279491175600385, 7280569108529861),
  (914099, 920813, 5363626148344723, 7348697661457107),
  (920813, 927596, 5417657843646709, 7435303216287571),
  (927596, 934355, 5493016620395766, 7488691241490470),
  (934355, 941169, 5539434095892831, 7558856026431678)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (900629, 907371, 5189115101719270, 7206232182270911) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (907371, 914099, 5279491175600385, 7280569108529861) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (914099, 920813, 5363626148344723, 7348697661457107) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (920813, 927596, 5417657843646709, 7435303216287571) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (927596, 934355, 5493016620395766, 7488691241490470) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (934355, 941169, 5539434095892831, 7558856026431678) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C025
