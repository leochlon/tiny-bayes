import PRO.B.C0

/-! Kernel check `q` of layer 5 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q5 : qCheck (LL 5) B.C0.X5 B.C0.Q5 = true := by decide +kernel

end PRO.K
