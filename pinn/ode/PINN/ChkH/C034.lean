import PINN.Interval

/-! Pieces 204..209 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C034

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1263674, 1270381, 2078652769885924, 4073743967538329),
  (1270381, 1277077, 1929258837066339, 3918016710182566),
  (1277077, 1283778, 1774249537655944, 3766282381675894),
  (1283778, 1290514, 1609775657662692, 3621536869028916),
  (1290514, 1297222, 1462589685207903, 3458147053504091),
  (1297222, 1303971, 1294939492456552, 3314021309888897)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1263674, 1270381, 2078652769885924, 4073743967538329) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1270381, 1277077, 1929258837066339, 3918016710182566) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1277077, 1283778, 1774249537655944, 3766282381675894) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1283778, 1290514, 1609775657662692, 3621536869028916) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1290514, 1297222, 1462589685207903, 3458147053504091) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1297222, 1303971, 1294939492456552, 3314021309888897) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C034
