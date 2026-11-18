import PRO.B.C0
import PRO.K.C0_o2
import PRO.K.C0_o5

/-! Kernel check `h` of layer 2 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h2 : hCheck (LL 2) B.C0.X2 B.C0.H2 = true := by decide +kernel

end PRO.K
