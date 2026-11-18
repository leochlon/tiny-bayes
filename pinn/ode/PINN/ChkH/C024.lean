import PINN.Interval

/-! Pieces 144..149 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C024

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (865384, 872034, 4666796309917115, 6670451680312061),
  (872034, 873813, 5657701848181496, 5822790415152678),
  (873813, 880469, 4810823593725065, 6808530002028456),
  (880469, 887189, 4901286199860121, 6928887524413867),
  (887189, 893909, 5005234390616978, 7025093272692220),
  (893909, 900629, 5103288300726119, 7115372725445106)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (865384, 872034, 4666796309917115, 6670451680312061) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (872034, 873813, 5657701848181496, 5822790415152678) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (873813, 880469, 4810823593725065, 6808530002028456) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (880469, 887189, 4901286199860121, 6928887524413867) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (887189, 893909, 5005234390616978, 7025093272692220) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (893909, 900629, 5103288300726119, 7115372725445106) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C024
