import CON.K.BosBoxes
import CON.K.BosO1

/-! Kernel check for layer 2 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o2 : outCheck z2 B2 A2 H2 B3 = true := by decide +kernel
end Bos
end CON
