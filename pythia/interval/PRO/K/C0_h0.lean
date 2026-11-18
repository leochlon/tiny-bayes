import PRO.B.C0
import PRO.K.C0_o0
import PRO.K.C0_o3

/-! Kernel check `h` of layer 0 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_h0 : hCheck (LL 0) (vecI (embRow 0) 128) B.C0.H0 = true := by decide +kernel

end PRO.K
