import PINN.Interval

/-! Pieces 42..47 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C007

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (234939, 240943, 12552722483918, 2014484888862823),
  (240943, 246988, -269201774512241, 1755398876365260),
  (246988, 253025, -534091002667028, 1481412032563403),
  (253025, 259080, -804345038455992, 1217456978519522),
  (259080, 262144, -283999887841989, 298521227190076),
  (262144, 268224, -1204438680806415, 823738434516009)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (234939, 240943, 12552722483918, 2014484888862823) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (240943, 246988, -269201774512241, 1755398876365260) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (246988, 253025, -534091002667028, 1481412032563403) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (253025, 259080, -804345038455992, 1217456978519522) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (259080, 262144, -283999887841989, 298521227190076) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (262144, 268224, -1204438680806415, 823738434516009) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C007
