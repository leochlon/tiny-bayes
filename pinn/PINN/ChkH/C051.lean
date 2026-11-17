import PINN.Interval

/-! Pieces 306..311 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C051

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1949717, 1956519, -1468843715196342, 537338981179526),
  (1956519, 1963280, -1325304000374268, 659804116029313),
  (1963280, 1970090, -1205252366274360, 809307795705327),
  (1970090, 1976910, -1072027815188226, 949990008100242),
  (1976910, 1983712, -929342208880430, 1084011368750006),
  (1983712, 1990532, -795507672553349, 1229653060352444)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1949717, 1956519, -1468843715196342, 537338981179526) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1956519, 1963280, -1325304000374268, 659804116029313) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1963280, 1970090, -1205252366274360, 809307795705327) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1970090, 1976910, -1072027815188226, 949990008100242) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1976910, 1983712, -929342208880430, 1084011368750006) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1983712, 1990532, -795507672553349, 1229653060352444) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C051
