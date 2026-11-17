import PINN.Interval

/-! Pieces 426..431 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C071

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2985173, 2999381, -2145827005739938, -501064078849204),
  (2999381, 3013662, -2351168942684773, -703888002075488),
  (3013662, 3027974, -2552393608957383, -912430927742656),
  (3027974, 3042447, -2768361647436944, -1108178475169172),
  (3042447, 3056979, -2973681764051492, -1316080507153298),
  (3056979, 3058346, -2273713747318788, -2241499418126563)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2985173, 2999381, -2145827005739938, -501064078849204) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2999381, 3013662, -2351168942684773, -703888002075488) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (3013662, 3027974, -2552393608957383, -912430927742656) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (3027974, 3042447, -2768361647436944, -1108178475169172) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (3042447, 3056979, -2973681764051492, -1316080507153298) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (3056979, 3058346, -2273713747318788, -2241499418126563) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C071
