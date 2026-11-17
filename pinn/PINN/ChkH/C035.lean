import PINN.Interval

/-! Pieces 210..215 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C035

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1303971, 1310720, 1138453454338372, 3157128915123146),
  (1310720, 1317440, 990669886771819, 2991847182639769),
  (1317440, 1324160, 834806334208500, 2835304416678775),
  (1324160, 1330880, 679133133391299, 2678819879375459),
  (1330880, 1337600, 523791582918121, 2522536845753065),
  (1337600, 1344335, 364317678709681, 2370883559090309)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1303971, 1310720, 1138453454338372, 3157128915123146) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1310720, 1317440, 990669886771819, 2991847182639769) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1317440, 1324160, 834806334208500, 2835304416678775) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1324160, 1330880, 679133133391299, 2678819879375459) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1330880, 1337600, 523791582918121, 2522536845753065) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1337600, 1344335, 364317678709681, 2370883559090309) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C035
