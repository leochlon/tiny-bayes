import CON.K.BosBoxes
import CON.K.BosO2

/-! Kernel check for layer 3 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o3 : outCheck z3 B3 A3 H3 B4 = true := by decide +kernel
end Bos
end CON
