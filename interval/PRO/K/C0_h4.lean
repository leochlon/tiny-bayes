import PRO.B.C0
import PRO.K.C0_h1

/-! Kernel check `h` of layer 4 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h4 : hCheck (LL 4) B.C0.X4 B.C0.H4 = true := by decide +kernel

end PRO.K
