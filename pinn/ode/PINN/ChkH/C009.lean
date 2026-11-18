import PINN.Interval

/-! Pieces 54..59 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C009

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (304836, 310946, -2874728738103240, -887914431235624),
  (310946, 317124, -3104534076194200, -1086366553930317),
  (317124, 323326, -3313431206540707, -1291531477613624),
  (323326, 329517, -3502601192009586, -1498659023159885),
  (329517, 335690, -3679558008231615, -1698387288904489),
  (335690, 341959, -3882850162700193, -1854760248750286)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (304836, 310946, -2874728738103240, -887914431235624) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (310946, 317124, -3104534076194200, -1086366553930317) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (317124, 323326, -3313431206540707, -1291531477613624) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (323326, 329517, -3502601192009586, -1498659023159885) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (329517, 335690, -3679558008231615, -1698387288904489) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (335690, 341959, -3882850162700193, -1854760248750286) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C009
