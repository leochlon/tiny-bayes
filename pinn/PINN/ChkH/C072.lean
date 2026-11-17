import PINN.Interval

/-! Pieces 432..437 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C072

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2796202, 2802986, 1749811878953645, 3769831132010590),
  (2802986, 2809770, 1595894479841285, 3616255917813775),
  (2809770, 2816554, 1441183478278078, 3461757051041748),
  (2816554, 2823338, 1285792363930937, 3306438280940899),
  (2823338, 2830103, 1135362084799691, 3145355339244154),
  (2830103, 2836893, 972098582589991, 2995910476993865)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2796202, 2802986, 1749811878953645, 3769831132010590) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2802986, 2809770, 1595894479841285, 3616255917813775) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2809770, 2816554, 1441183478278078, 3461757051041748) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2816554, 2823338, 1285792363930937, 3306438280940899) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2823338, 2830103, 1135362084799691, 3145355339244154) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2830103, 2836893, 972098582589991, 2995910476993865) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C072
