import PINN.Interval

/-! Pieces 474..479 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C079

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3079082, 3085994, -4036286812387740, -2038430135423018),
  (3085994, 3092935, -4132621755418017, -2122346245203438),
  (3092935, 3099844, -4207382182728872, -2219510980701961),
  (3099844, 3106833, -4309761186412791, -2281119168433513),
  (3106833, 3113822, -4385568670009002, -2361433452310944),
  (3113822, 3120802, -4454990585944160, -2439007892526049)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3079082, 3085994, -4036286812387740, -2038430135423018) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3085994, 3092935, -4132621755418017, -2122346245203438) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3092935, 3099844, -4207382182728872, -2219510980701961) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3099844, 3106833, -4309761186412791, -2281119168433513) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3106833, 3113822, -4385568670009002, -2361433452310944) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3113822, 3120802, -4454990585944160, -2439007892526049) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C079
