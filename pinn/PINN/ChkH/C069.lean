import PINN.Interval

/-! Pieces 414..419 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C069

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2676103, 2682940, 4209169582698942, 6233194720532474),
  (2682940, 2689714, 4104715242910179, 6094863905110722),
  (2689714, 2696505, 3974948909276595, 5977386301560825),
  (2696505, 2703335, 3836095691008235, 5862776021154707),
  (2703335, 2708821, 4067876796474390, 5397540475611972),
  (2708821, 2715605, 3612411919791263, 5616490790825276)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2676103, 2682940, 4209169582698942, 6233194720532474) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2682940, 2689714, 4104715242910179, 6094863905110722) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2689714, 2696505, 3974948909276595, 5977386301560825) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2696505, 2703335, 3836095691008235, 5862776021154707) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2703335, 2708821, 4067876796474390, 5397540475611972) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2708821, 2715605, 3612411919791263, 5616490790825276) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C069
