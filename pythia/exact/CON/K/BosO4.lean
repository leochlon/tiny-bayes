import CON.K.BosBoxes
import CON.K.BosO3

/-! Kernel check for layer 4 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o4 : outCheck z4 B4 A4 H4 B5 = true := by decide +kernel
end Bos
end CON
