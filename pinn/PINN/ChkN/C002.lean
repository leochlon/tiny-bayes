import PINN.Interval

/-! Pieces 12..17 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C002

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (14576, 15920, -35553250567413221, -33902861314922064),
  (15920, 17280, -34008549578834275, -32367469340024300),
  (17280, 18672, -32476810065177437, -30825682953401031),
  (18672, 20096, -30940111191378975, -29280639739093404),
  (20096, 21536, -29399021541377408, -27752360130251797),
  (21536, 23008, -27874597320444923, -26222315653817176)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (14576, 15920, -35553250567413221, -33902861314922064) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (15920, 17280, -34008549578834275, -32367469340024300) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (17280, 18672, -32476810065177437, -30825682953401031) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (18672, 20096, -30940111191378975, -29280639739093404) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (20096, 21536, -29399021541377408, -27752360130251797) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (21536, 23008, -27874597320444923, -26222315653817176) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C002
