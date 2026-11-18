import PRO.B.C0

/-! Kernel check `q` of layer 0 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q0 : qCheck (LL 0) (vecI (embRow 0) 128) B.C0.Q0 = true := by decide +kernel

end PRO.K
