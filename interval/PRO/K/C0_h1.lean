import PRO.B.C0
import PRO.K.C0_o1
import PRO.K.C0_o4

/-! Kernel check `h` of layer 1 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h1 : hCheck (LL 1) B.C0.X1 B.C0.H1 = true := by decide +kernel

end PRO.K
