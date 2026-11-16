import PRO.B.C0
import PRO.K.C0_q1

/-! Kernel check `a` of layer 1 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_a1 : aCheck (LL 1) 0 [B.C0.Q1] B.C0.A1 = true := by decide +kernel

end PRO.K
