import PRO.B.C0
import PRO.K.C0_a3

/-! Kernel check `o` of layer 3 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o3 : oCheck (LL 3) B.C0.X3 B.C0.A3 B.C0.H3 B.C0.X4 = true := by decide +kernel

end PRO.K
