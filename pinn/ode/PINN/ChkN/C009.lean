import PINN.Interval

/-! Pieces 54..59 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C009

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (111509, 116204, 16659210900467199, 18303664069330776),
  (116204, 121121, 16989007758092514, 18637472217055878),
  (121121, 126254, 17200989724136275, 18846745315319009),
  (126254, 131607, 17283820733745216, 18927791448329388),
  (131607, 136790, 17240209187571574, 18874474998952501),
  (136790, 141833, 17067106018435711, 18723154243229086)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (111509, 116204, 16659210900467199, 18303664069330776) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (116204, 121121, 16989007758092514, 18637472217055878) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (121121, 126254, 17200989724136275, 18846745315319009) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (126254, 131607, 17283820733745216, 18927791448329388) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (131607, 136790, 17240209187571574, 18874474998952501) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (136790, 141833, 17067106018435711, 18723154243229086) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C009
