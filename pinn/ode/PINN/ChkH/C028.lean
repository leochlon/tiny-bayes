import PINN.Interval

/-! Pieces 168..173 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C028

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1023265, 1030186, 5727252084089688, 7755790142739256),
  (1030186, 1037082, 5704342902756322, 7722408779333669),
  (1037082, 1043906, 5689252703589187, 7669961881320743),
  (1043906, 1048576, 6177746868185778, 7116079621511389),
  (1048576, 1055424, 5609435831302734, 7610918203830679),
  (1055424, 1062272, 5558636477479932, 7564160675384347)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1023265, 1030186, 5727252084089688, 7755790142739256) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1030186, 1037082, 5704342902756322, 7722408779333669) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1037082, 1043906, 5689252703589187, 7669961881320743) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1043906, 1048576, 6177746868185778, 7116079621511389) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1048576, 1055424, 5609435831302734, 7610918203830679) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1055424, 1062272, 5558636477479932, 7564160675384347) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C028
