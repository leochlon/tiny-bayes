import PINN.Interval

/-! Pieces 534..539 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C089

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3480951, 3487543, -798887471120665, 1208328233466670),
  (3487543, 3494108, -601096197342473, 1394831362599215),
  (3494108, 3495253, 466261615231855, 555500388916369),
  (3495253, 3501845, -381596735252431, 1634240160199255),
  (3501845, 3508437, -184532308276490, 1835030038412479),
  (3508437, 3515029, 15335363576832, 2038442565159123)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3480951, 3487543, -798887471120665, 1208328233466670) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3487543, 3494108, -601096197342473, 1394831362599215) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3494108, 3495253, 466261615231855, 555500388916369) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3495253, 3501845, -381596735252431, 1634240160199255) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3501845, 3508437, -184532308276490, 1835030038412479) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3508437, 3515029, 15335363576832, 2038442565159123) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C089
