import PINN.Interval

/-! Pieces 132..137 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C022

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (786432, 792960, 2934400985704640, 4947204965428373),
  (792960, 799488, 3105284430462664, 5112103769425094),
  (799488, 806016, 3272175241561636, 5272866455194669),
  (806016, 812544, 3434911582508159, 5429346226448545),
  (812544, 819125, 3578217572442304, 5597743373351105),
  (819125, 825693, 3737279178696348, 5742254521961793)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (786432, 792960, 2934400985704640, 4947204965428373) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (792960, 799488, 3105284430462664, 5112103769425094) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (799488, 806016, 3272175241561636, 5272866455194669) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (806016, 812544, 3434911582508159, 5429346226448545) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (812544, 819125, 3578217572442304, 5597743373351105) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (819125, 825693, 3737279178696348, 5742254521961793) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C022
