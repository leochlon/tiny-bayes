import PINN.Interval

/-! Pieces 24..29 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C004

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (32487, 34189, -17319517070643207, -15667920473235406),
  (34189, 35929, -15837866904978020, -14187997754135934),
  (35929, 37712, -14366760654606325, -12714604902259627),
  (37712, 39531, -12901373149405352, -11257135024372256),
  (39531, 41400, -11452653475981878, -9804506947112217),
  (41400, 43330, -10010887780390741, -8351867764256501)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (32487, 34189, -17319517070643207, -15667920473235406) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (34189, 35929, -15837866904978020, -14187997754135934) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (35929, 37712, -14366760654606325, -12714604902259627) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (37712, 39531, -12901373149405352, -11257135024372256) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (39531, 41400, -11452653475981878, -9804506947112217) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (41400, 43330, -10010887780390741, -8351867764256501) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C004
