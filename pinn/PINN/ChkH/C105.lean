import PINN.Interval

/-! Pieces 630..635 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C105

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (4084279, 4089940, -2027963315467059, -28170444403904),
  (4089940, 4095578, -2656922289583385, -649196562848237),
  (4095578, 4101205, -3309690123579728, -1285732404840618),
  (4101205, 4106787, -3970586494894231, -1951562814321861),
  (4106787, 4106922, -3316721577301034, -3298877086531343),
  (4106922, 4112426, -4653106422190652, -2658063180672356)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (4084279, 4089940, -2027963315467059, -28170444403904) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (4089940, 4095578, -2656922289583385, -649196562848237) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (4095578, 4101205, -3309690123579728, -1285732404840618) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (4101205, 4106787, -3970586494894231, -1951562814321861) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (4106787, 4106922, -3316721577301034, -3298877086531343) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (4106922, 4112426, -4653106422190652, -2658063180672356) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C105
