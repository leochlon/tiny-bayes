import PRO.B.C0
import PRO.K.C0_h0

/-! Kernel check `h` of layer 3 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h3 : hCheck (LL 3) B.C0.X3 B.C0.H3 = true := by decide +kernel

end PRO.K
