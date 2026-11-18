import PRO.B.C0

/-! Kernel check `q` of layer 3 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q3 : qCheck (LL 3) B.C0.X3 B.C0.Q3 = true := by decide +kernel

end PRO.K
