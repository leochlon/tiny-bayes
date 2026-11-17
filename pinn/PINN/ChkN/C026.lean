import PINN.Interval

/-! Pieces 156..161 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C026

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (593414, 598904, 649187781449388, 2279315041074191),
  (598904, 604439, 925686782039324, 2562022098863953),
  (604439, 610030, 1190343181267723, 2837766817678371),
  (610030, 611669, 2086060385737051, 2280000472639223),
  (611669, 617301, 1525927792361416, 3169360823239774),
  (617301, 622997, 1764320848431515, 3422143369210350)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (593414, 598904, 649187781449388, 2279315041074191) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (598904, 604439, 925686782039324, 2562022098863953) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (604439, 610030, 1190343181267723, 2837766817678371) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (610030, 611669, 2086060385737051, 2280000472639223) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (611669, 617301, 1525927792361416, 3169360823239774) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (617301, 622997, 1764320848431515, 3422143369210350) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C026
