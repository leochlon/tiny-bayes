import PINN.Interval

/-! Pieces 30..35 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C005

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (168549, 174615, 2818024468942910, 4820911191420694),
  (174615, 174762, 3704314007320569, 3710879806053701),
  (174762, 180842, 2581211907090810, 4603381618575937),
  (180842, 186858, 2364787448204010, 4355557240241412),
  (186858, 192874, 2120883288187541, 4118696536323600),
  (192874, 198890, 1869625536304439, 3873085249562974)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (168549, 174615, 2818024468942910, 4820911191420694) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (174615, 174762, 3704314007320569, 3710879806053701) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (174762, 180842, 2581211907090810, 4603381618575937) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (180842, 186858, 2364787448204010, 4355557240241412) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (186858, 192874, 2120883288187541, 4118696536323600) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (192874, 198890, 1869625536304439, 3873085249562974) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C005
