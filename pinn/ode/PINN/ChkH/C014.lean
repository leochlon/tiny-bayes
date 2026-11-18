import PINN.Interval

/-! Pieces 84..89 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C014

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (489463, 495993, -5031644616409125, -3004592653819841),
  (495993, 502513, -4949848309668047, -2922480226701266),
  (502513, 508977, -4845629949987394, -2846155268080395),
  (508977, 515436, -4748951635643398, -2746443717907756),
  (515436, 521867, -4637266744780539, -2646208795707513),
  (521867, 524288, -3719384889228547, -3409608437223377)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (489463, 495993, -5031644616409125, -3004592653819841) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (495993, 502513, -4949848309668047, -2922480226701266) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (502513, 508977, -4845629949987394, -2846155268080395) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (508977, 515436, -4748951635643398, -2746443717907756) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (515436, 521867, -4637266744780539, -2646208795707513) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (521867, 524288, -3719384889228547, -3409608437223377) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C014
