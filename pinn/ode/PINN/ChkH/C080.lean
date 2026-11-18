import PINN.Interval

/-! Pieces 480..485 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C080

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3120802, 3127714, -4503080975982175, -2527955017319839),
  (3127714, 3134679, -4580675122411690, -2577966519723110),
  (3134679, 3141671, -4646251486724737, -2631221538569266),
  (3141671, 3145728, -4027906753315990, -3336744697447263),
  (3145728, 3152704, -4723504780618092, -2722059452135652),
  (3152704, 3159680, -4768711246842834, -2770222059156603)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3120802, 3127714, -4503080975982175, -2527955017319839) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3127714, 3134679, -4580675122411690, -2577966519723110) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3134679, 3141671, -4646251486724737, -2631221538569266) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3141671, 3145728, -4027906753315990, -3336744697447263) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3145728, 3152704, -4723504780618092, -2722059452135652) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3152704, 3159680, -4768711246842834, -2770222059156603) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C080
