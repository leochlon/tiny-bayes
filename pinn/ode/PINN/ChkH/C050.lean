import PINN.Interval

/-! Pieces 300..305 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C050

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1910424, 1917247, -2200418124178710, -195542815983492),
  (1917247, 1922389, -1672378087787546, -509810755293122),
  (1922389, 1929237, -1993920672712232, 29483777712329),
  (1929237, 1936085, -1868695967103401, 157167373829190),
  (1936085, 1942933, -1741287576776230, 286911590979463),
  (1942933, 1949717, -1594125133572974, 399726242350286)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1910424, 1917247, -2200418124178710, -195542815983492) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1917247, 1922389, -1672378087787546, -509810755293122) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1922389, 1929237, -1993920672712232, 29483777712329) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1929237, 1936085, -1868695967103401, 157167373829190) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1936085, 1942933, -1741287576776230, 286911590979463) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1942933, 1949717, -1594125133572974, 399726242350286) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C050
