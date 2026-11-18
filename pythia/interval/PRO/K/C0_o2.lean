import PRO.B.C0
import PRO.K.C0_a2

/-! Kernel check `o` of layer 2 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o2 : oCheck (LL 2) B.C0.X2 B.C0.A2 B.C0.H2 B.C0.X3 = true := by decide +kernel

end PRO.K
