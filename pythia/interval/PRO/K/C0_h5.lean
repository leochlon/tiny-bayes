import PRO.B.C0
import PRO.K.C0_h2

/-! Kernel check `h` of layer 5 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h5 : hCheck (LL 5) B.C0.X5 B.C0.H5 = true := by decide +kernel

end PRO.K
