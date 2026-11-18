import PINN.Interval

/-! Pieces 78..83 of the certificate for `û`, kernel-checked. -/

namespace PINN.ChkH.C013

/-- Pieces `(a, b, lo, hi)`: `[a, b] / 2^20`, bounds `[lo, hi] / 2^64`. -/
def L : List PINN.Piece := [
  (450090, 456682, -5320318583481353, -3299856437145106),
  (456682, 463274, -5300954206085361, -3272399785634858),
  (463274, 469827, -5259226466136314, -3246331315468889),
  (469827, 476368, -5215331131107367, -3202213395210053),
  (476368, 482919, -5168038417101910, -3141569639509227),
  (482919, 489463, -5105559106291311, -3076669640939387)]

set_option maxHeartbeats 0 in
theorem ok0 : PINN.okRH (450090, 456682, -5320318583481353, -3299856437145106) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : PINN.okRH (456682, 463274, -5300954206085361, -3272399785634858) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : PINN.okRH (463274, 469827, -5259226466136314, -3246331315468889) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : PINN.okRH (469827, 476368, -5215331131107367, -3202213395210053) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : PINN.okRH (476368, 482919, -5168038417101910, -3141569639509227) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : PINN.okRH (482919, 489463, -5105559106291311, -3076669640939387) = true := by
  decide +kernel

theorem ok : L.all PINN.okRH = true := by
  simp only [L, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, Bool.and_self, Bool.and_true]

end PINN.ChkH.C013
