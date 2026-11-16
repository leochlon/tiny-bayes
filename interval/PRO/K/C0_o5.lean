import PRO.B.C0
import PRO.K.C0_a5

/-! Kernel check `o` of layer 5 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o5 : oCheck (LL 5) B.C0.X5 B.C0.A5 B.C0.H5 B.C0.X6 = true := by decide +kernel

end PRO.K
