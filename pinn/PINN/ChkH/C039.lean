import PINN.Interval

/-! Pieces 234..239 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C039

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1465920, 1472720, -2345331638267029, -344128899958694),
  (1472720, 1479499, -2459287000946949, -472958911514423),
  (1479499, 1485482, -2356031609440974, -798987970088902),
  (1485482, 1492330, -2696322949360690, -677245328539697),
  (1492330, 1499178, -2808085046605246, -792539204242074),
  (1499178, 1506026, -2916516498886442, -904576815993980)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1465920, 1472720, -2345331638267029, -344128899958694) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1472720, 1479499, -2459287000946949, -472958911514423) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1479499, 1485482, -2356031609440974, -798987970088902) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1485482, 1492330, -2696322949360690, -677245328539697) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1492330, 1499178, -2808085046605246, -792539204242074) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1499178, 1506026, -2916516498886442, -904576815993980) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C039
