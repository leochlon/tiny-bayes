import PINN.Interval

/-! Pieces 582..587 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C097

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3777365, 3784021, 8058460023898847, 10062904861046223),
  (3784021, 3790725, 8164224132253609, 10188927248822374),
  (3790725, 3797429, 8275970428965924, 10292352851890364),
  (3797429, 3804087, 8391874265726453, 10372741297619282),
  (3804087, 3810842, 8456979306842989, 10485658882731252),
  (3810842, 3817602, 8540171340326016, 10561802958489900)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3777365, 3784021, 8058460023898847, 10062904861046223) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3784021, 3790725, 8164224132253609, 10188927248822374) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3790725, 3797429, 8275970428965924, 10292352851890364) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3797429, 3804087, 8391874265726453, 10372741297619282) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3804087, 3810842, 8456979306842989, 10485658882731252) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3810842, 3817602, 8540171340326016, 10561802958489900) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C097
