import PRO.B.C0
import PRO.K.C0_q0

/-! Kernel check `a` of layer 0 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a0 : aCheck (LL 0) 0 [B.C0.Q0] B.C0.A0 = true := by decide +kernel

end PRO.K
