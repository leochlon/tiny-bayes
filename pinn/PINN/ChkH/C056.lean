import PINN.Interval

/-! Pieces 336..341 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C056

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2151377, 2158176, 2779669299613490, 4791664276764836),
  (2158176, 2164971, 2918694538779303, 4927589700710899),
  (2164971, 2171771, 3053879692331050, 5064396142438596),
  (2171771, 2178550, 3194483981450714, 5192215761497054),
  (2178550, 2184533, 3533500063893366, 5102392483536447),
  (2184533, 2191317, 3442021922907660, 5440015874658732)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (2151377, 2158176, 2779669299613490, 4791664276764836) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (2158176, 2164971, 2918694538779303, 4927589700710899) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (2164971, 2171771, 3053879692331050, 5064396142438596) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (2171771, 2178550, 3194483981450714, 5192215761497054) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (2178550, 2184533, 3533500063893366, 5102392483536447) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (2184533, 2191317, 3442021922907660, 5440015874658732) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C056
