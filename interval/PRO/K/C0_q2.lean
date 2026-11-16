import PRO.B.C0

/-! Kernel check `q` of layer 2 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q2 : qCheck (LL 2) B.C0.X2 B.C0.Q2 = true := by decide +kernel

end PRO.K
