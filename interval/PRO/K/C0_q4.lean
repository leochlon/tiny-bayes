import PRO.B.C0

/-! Kernel check `q` of layer 4 for the position column C0. -/

namespace PRO.K

set_option maxHeartbeats 0 in
theorem C0_q4 : qCheck (LL 4) B.C0.X4 B.C0.Q4 = true := by decide +kernel

end PRO.K
