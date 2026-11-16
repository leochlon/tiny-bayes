import PRO.B.C0

/-! Kernel check `q` of layer 1 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q1 : qCheck (LL 1) B.C0.X1 B.C0.Q1 = true := by decide +kernel

end PRO.K
