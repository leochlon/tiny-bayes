import PINN.Interval

/-! Pieces 408..413 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C068

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2762426, 2775883, 748463120430333, 2386854256903533),
  (2775883, 2789375, 602960763238093, 2241616386394575),
  (2789375, 2796202, 1081162990808589, 1537521110875982),
  (2796202, 2809770, 371111476450684, 2015239515038806),
  (2809770, 2823338, 216568710747701, 1852372398013633),
  (2823338, 2836987, 47831258372388, 1693713663941658)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2762426, 2775883, 748463120430333, 2386854256903533) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2775883, 2789375, 602960763238093, 2241616386394575) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2789375, 2796202, 1081162990808589, 1537521110875982) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2796202, 2809770, 371111476450684, 2015239515038806) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2809770, 2823338, 216568710747701, 1852372398013633) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2823338, 2836987, 47831258372388, 1693713663941658) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C068
