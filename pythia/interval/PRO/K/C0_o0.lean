import PRO.B.C0
import PRO.K.C0_a0

/-! Kernel check `o` of layer 0 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_o0 : oCheck (LL 0) (vecI (embRow 0) 128) B.C0.A0 B.C0.H0 B.C0.X1 = true := by decide +kernel

end PRO.K
