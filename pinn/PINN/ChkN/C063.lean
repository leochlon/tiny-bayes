import PINN.Interval

/-! Pieces 378..383 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C063

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2396260, 2408766, 2288747419920969, 3947329787951193),
  (2408766, 2421205, 2331226697571701, 3955199088447523),
  (2421205, 2433841, 2334865267101787, 3992441131053441),
  (2433841, 2446476, 2359427783597952, 3998897424682414),
  (2446476, 2446677, 3184721161313480, 3185354458583665),
  (2446677, 2459349, 2374294303855859, 4004807810460890)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2396260, 2408766, 2288747419920969, 3947329787951193) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2408766, 2421205, 2331226697571701, 3955199088447523) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2421205, 2433841, 2334865267101787, 3992441131053441) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2433841, 2446476, 2359427783597952, 3998897424682414) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2446476, 2446677, 3184721161313480, 3185354458583665) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2446677, 2459349, 2374294303855859, 4004807810460890) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C063
