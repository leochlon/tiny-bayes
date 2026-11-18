import PRO.B.C0
import PRO.K.C0_a4

/-! Kernel check `o` of layer 4 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o4 : oCheck (LL 4) B.C0.X4 B.C0.A4 B.C0.H4 B.C0.X5 = true := by decide +kernel

end PRO.K
