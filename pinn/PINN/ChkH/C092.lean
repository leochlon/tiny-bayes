import PINN.Interval

/-! Pieces 552..557 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C092

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3589162, 3595690, 2642591633055616, 4655775405421664),
  (3595690, 3602218, 2860942259875894, 4874902171679469),
  (3602218, 3608746, 3079437749468579, 5093931781247972),
  (3608746, 3615267, 3299607096221702, 5310611935135010),
  (3615267, 3621790, 3516943814031925, 5529150275466347),
  (3621790, 3628289, 3740932071910285, 5738990505412976)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3589162, 3595690, 2642591633055616, 4655775405421664) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3595690, 3602218, 2860942259875894, 4874902171679469) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3602218, 3608746, 3079437749468579, 5093931781247972) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3608746, 3615267, 3299607096221702, 5310611935135010) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3615267, 3621790, 3516943814031925, 5529150275466347) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3621790, 3628289, 3740932071910285, 5738990505412976) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C092
