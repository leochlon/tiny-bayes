import PRO.B.C0
import PRO.K.C0_q5

/-! Kernel check `a` of layer 5 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a5 : aCheck (LL 5) 0 [B.C0.Q5] B.C0.A5 = true := by decide +kernel

end PRO.K
