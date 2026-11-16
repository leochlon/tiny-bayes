import PRO.B.C0
import PRO.K.C0_a1

/-! Kernel check `o` of layer 1 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o1 : oCheck (LL 1) B.C0.X1 B.C0.A1 B.C0.H1 B.C0.X2 = true := by decide +kernel

end PRO.K
