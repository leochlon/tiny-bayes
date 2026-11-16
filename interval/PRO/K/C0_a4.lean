import PRO.B.C0
import PRO.K.C0_q4

/-! Kernel check `a` of layer 4 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a4 : aCheck (LL 4) 0 [B.C0.Q4] B.C0.A4 = true := by decide +kernel

end PRO.K
