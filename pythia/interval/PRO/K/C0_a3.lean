import PRO.B.C0
import PRO.K.C0_q3

/-! Kernel check `a` of layer 3 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a3 : aCheck (LL 3) 0 [B.C0.Q3] B.C0.A3 = true := by decide +kernel

end PRO.K
