import PINN.Interval

/-! Pieces 102..107 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C017

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (601207, 607581, -2622134058506121, -622839868862796),
  (607581, 611669, -1904477980217203, -1039231693074417),
  (611669, 618069, -2326912083242394, -310578830206335),
  (618069, 624469, -2137680235145278, -120861258271036),
  (624469, 630869, -1945723660844120, 71289571066181),
  (630869, 637269, -1751347435780722, 265567978615561)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (601207, 607581, -2622134058506121, -622839868862796) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (607581, 611669, -1904477980217203, -1039231693074417) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (611669, 618069, -2326912083242394, -310578830206335) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (618069, 624469, -2137680235145278, -120861258271036) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (624469, 630869, -1945723660844120, 71289571066181) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (630869, 637269, -1751347435780722, 265567978615561) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C017
