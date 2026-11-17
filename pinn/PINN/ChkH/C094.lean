import PINN.Interval

/-! Pieces 564..569 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C094

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3667455, 3670016, 5981661654145834, 6339923952484876),
  (3670016, 3676544, 5300846637616523, 7305679543890540),
  (3676544, 3683072, 5504352535254287, 7506668050021960),
  (3683072, 3689600, 5704820320537245, 7704588885538593),
  (3689600, 3696128, 5901970543205973, 7899147982596074),
  (3696128, 3702709, 6080791168665463, 8106318901618955)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3667455, 3670016, 5981661654145834, 6339923952484876) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3670016, 3676544, 5300846637616523, 7305679543890540) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3676544, 3683072, 5504352535254287, 7506668050021960) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3683072, 3689600, 5704820320537245, 7704588885538593) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3689600, 3696128, 5901970543205973, 7899147982596074) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3696128, 3702709, 6080791168665463, 8106318901618955) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C094
