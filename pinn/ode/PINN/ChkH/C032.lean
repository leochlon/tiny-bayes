import PINN.Interval

/-! Pieces 192..197 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C032

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (1183395, 1190182, 3764718198837103, 5792243939293186),
  (1190182, 1196917, 3647448577915197, 5646917676251138),
  (1196917, 1203626, 3520778325400855, 5507084219737671),
  (1203626, 1210402, 3364637106573079, 5390762642700963),
  (1210402, 1217173, 3225911822298423, 5250936159700843),
  (1217173, 1223338, 3257509840173286, 4949048201460198)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (1183395, 1190182, 3764718198837103, 5792243939293186) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (1190182, 1196917, 3647448577915197, 5646917676251138) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (1196917, 1203626, 3520778325400855, 5507084219737671) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (1203626, 1210402, 3364637106573079, 5390762642700963) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (1210402, 1217173, 3225911822298423, 5250936159700843) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (1217173, 1223338, 3257509840173286, 4949048201460198) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C032
