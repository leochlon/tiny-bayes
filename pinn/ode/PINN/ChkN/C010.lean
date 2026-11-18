import PINN.Interval

/-! Pieces 60..65 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C010

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (141833, 146721, 16811552214554214, 18464593713822657),
  (146721, 151486, 16473661226298627, 18131041040861602),
  (151486, 156122, 16077921421627422, 17724152126802149),
  (156122, 160672, 15618197000641473, 17270822880744020),
  (160672, 165130, 15117103672809399, 16764381723255481),
  (165130, 169531, 14567878793786281, 16225013789089661)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (141833, 146721, 16811552214554214, 18464593713822657) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (146721, 151486, 16473661226298627, 18131041040861602) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (151486, 156122, 16077921421627422, 17724152126802149) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (156122, 160672, 15618197000641473, 17270822880744020) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (160672, 165130, 15117103672809399, 16764381723255481) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (165130, 169531, 14567878793786281, 16225013789089661) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C010
