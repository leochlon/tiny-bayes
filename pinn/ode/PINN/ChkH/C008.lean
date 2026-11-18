import PINN.Interval

/-! Pieces 48..53 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C008

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (268224, 274304, -1459895226112959, 561473641930328),
  (274304, 280384, -1709946878192097, 303970611074140),
  (280384, 286464, -1954017663636452, 51847802672397),
  (286464, 292560, -2196829191522210, -189675211250572),
  (292560, 298679, -2435641623612478, -423089203545838),
  (298679, 304836, -2672505540768384, -646141977868995)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (268224, 274304, -1459895226112959, 561473641930328) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (274304, 280384, -1709946878192097, 303970611074140) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (280384, 286464, -1954017663636452, 51847802672397) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (286464, 292560, -2196829191522210, -189675211250572) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (292560, 298679, -2435641623612478, -423089203545838) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (298679, 304836, -2672505540768384, -646141977868995) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C008
