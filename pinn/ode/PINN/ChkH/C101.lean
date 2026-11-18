import PINN.Interval

/-! Pieces 606..611 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C101

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (3938688, 3945216, 7584834249779887, 9607529701586046),
  (3945216, 3951680, 7390494476676045, 9394206363539326),
  (3951680, 3958144, 7160227798607629, 9182842308122100),
  (3958144, 3964559, 6926673982571621, 8939937440114051),
  (3964559, 3970948, 6669285083522981, 8686578421304147),
  (3970948, 3977307, 6395288272845518, 8414492811598773)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (3938688, 3945216, 7584834249779887, 9607529701586046) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (3945216, 3951680, 7390494476676045, 9394206363539326) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (3951680, 3958144, 7160227798607629, 9182842308122100) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (3958144, 3964559, 6926673982571621, 8939937440114051) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (3964559, 3970948, 6669285083522981, 8686578421304147) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (3970948, 3977307, 6395288272845518, 8414492811598773) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C101
