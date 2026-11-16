import PRO.B.C0
import PRO.K.C0_q2

/-! Kernel check `a` of layer 2 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a2 : aCheck (LL 2) 0 [B.C0.Q2] B.C0.A2 = true := by decide +kernel

end PRO.K
