import PINN.Interval

/-! Pieces 390..395 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C065

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2516621, 2523568, 6126918870606484, 8131804308597549),
  (2523568, 2530533, 6078947879900034, 8098043840323603),
  (2530533, 2534058, 6789936114809893, 7319916606306928),
  (2534058, 2540970, 6021697227055905, 8016655348116870),
  (2540970, 2547882, 5968672591418153, 7967855332320358),
  (2547882, 2554794, 5911631341353864, 7914988973518026)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2516621, 2523568, 6126918870606484, 8131804308597549) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2523568, 2530533, 6078947879900034, 8098043840323603) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2530533, 2534058, 6789936114809893, 7319916606306928) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2534058, 2540970, 6021697227055905, 8016655348116870) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2540970, 2547882, 5968672591418153, 7967855332320358) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2547882, 2554794, 5911631341353864, 7914988973518026) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C065
