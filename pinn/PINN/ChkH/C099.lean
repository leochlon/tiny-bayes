import PINN.Interval

/-! Pieces 594..599 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C099

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3858474, 3865322, 8785044338338972, 10796968794691143),
  (3865322, 3872170, 8760614274737712, 10787054395589111),
  (3872170, 3878965, 8737230488453305, 10747692548311351),
  (3878965, 3885718, 8696285907285036, 10697225238797555),
  (3885718, 3892430, 8640499355409743, 10632507872035204),
  (3892430, 3899103, 8568902855284950, 10554123982788087)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3858474, 3865322, 8785044338338972, 10796968794691143) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3865322, 3872170, 8760614274737712, 10787054395589111) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3872170, 3878965, 8737230488453305, 10747692548311351) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3878965, 3885718, 8696285907285036, 10697225238797555) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3885718, 3892430, 8640499355409743, 10632507872035204) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3892430, 3899103, 8568902855284950, 10554123982788087) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C099
