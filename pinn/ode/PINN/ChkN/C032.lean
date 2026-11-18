import PINN.Interval

/-! Pieces 192..197 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C032

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (805440, 811776, 2850349335815332, 4497732494350039),
  (811776, 818136, 2706417246087383, 4363478192734017),
  (818136, 824497, 2562511573809671, 4217452524764317),
  (824497, 830854, 2415245386960042, 4064769620016355),
  (830854, 837230, 2258050510413898, 3912706161191215),
  (837230, 843588, 2106218075283654, 3747461818103986)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (805440, 811776, 2850349335815332, 4497732494350039) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (811776, 818136, 2706417246087383, 4363478192734017) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (818136, 824497, 2562511573809671, 4217452524764317) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (824497, 830854, 2415245386960042, 4064769620016355) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (830854, 837230, 2258050510413898, 3912706161191215) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (837230, 843588, 2106218075283654, 3747461818103986) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C032
