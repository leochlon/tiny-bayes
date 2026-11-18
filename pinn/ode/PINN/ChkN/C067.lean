import PINN.Interval

/-! Pieces 402..407 of the certificate for `N`, kernel-checked. -/

namespace PINN.ChkN.C067

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (2687507, 2700828, 1451634735449386, 3098385713868830),
  (2700828, 2708821, 1876319279364443, 2494973706209326),
  (2708821, 2722133, 1275769785636677, 2909195717225879),
  (2722133, 2735573, 1141890961393108, 2798498659819358),
  (2735573, 2748954, 1024038284057073, 2659591316039792),
  (2748954, 2762426, 882965624254215, 2532333529859710)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRN (2687507, 2700828, 1451634735449386, 3098385713868830) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRN (2700828, 2708821, 1876319279364443, 2494973706209326) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRN (2708821, 2722133, 1275769785636677, 2909195717225879) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRN (2722133, 2735573, 1141890961393108, 2798498659819358) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRN (2735573, 2748954, 1024038284057073, 2659591316039792) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRN (2748954, 2762426, 882965624254215, 2532333529859710) = true := by
  decide +kernel

theorem ok : L.all PINN.okRN = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkN.C067
