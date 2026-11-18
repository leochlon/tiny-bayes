import PINN.Interval

/-! Pieces 588..593 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C098

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3817602, 3824342, 8620208136285036, 10619980882208106),
  (3824342, 3831126, 8670969447171081, 10685884213453353),
  (3831126, 3837952, 8711493016624610, 10739882037114794),
  (3837952, 3844778, 8752804472302680, 10769455117012269),
  (3844778, 3851626, 8775517072006602, 10792822853454856),
  (3851626, 3858474, 8792018407036328, 10796571938679102)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3817602, 3824342, 8620208136285036, 10619980882208106) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3824342, 3831126, 8670969447171081, 10685884213453353) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3831126, 3837952, 8711493016624610, 10739882037114794) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3837952, 3844778, 8752804472302680, 10769455117012269) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3844778, 3851626, 8775517072006602, 10792822853454856) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3851626, 3858474, 8792018407036328, 10796571938679102) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C098
