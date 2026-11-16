import CON.K.BosBoxes
import CON.K.BosO0

/-! Kernel check for layer 1 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o1 : outCheck z1 B1 A1 H1 B2 = true := by decide +kernel
end Bos
end CON
