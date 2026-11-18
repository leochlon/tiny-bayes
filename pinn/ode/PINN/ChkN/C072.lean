import PINN.Interval

/-! Pieces 432..437 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C072

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3058346, 3072938, -3196938944297096, -1543677110526118),
  (3072938, 3087530, -3393510154931196, -1756370560196063),
  (3087530, 3102307, -3608278223860070, -1948869201282780),
  (3102307, 3117063, -3799305161052813, -2161826830583749),
  (3117063, 3131843, -3991620578615022, -2366965218728335),
  (3131843, 3145728, -4083295506403076, -2653831566209649)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (3058346, 3072938, -3196938944297096, -1543677110526118) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (3072938, 3087530, -3393510154931196, -1756370560196063) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3087530, 3102307, -3608278223860070, -1948869201282780) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3102307, 3117063, -3799305161052813, -2161826830583749) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3117063, 3131843, -3991620578615022, -2366965218728335) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3131843, 3145728, -4083295506403076, -2653831566209649) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C072
