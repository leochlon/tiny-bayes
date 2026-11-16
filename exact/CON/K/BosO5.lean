import CON.K.BosBoxes
import CON.K.BosO4

/-! Kernel check for layer 5 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o5 : outCheck z5 B5 A5 H5 B6 = true := by decide +kernel
end Bos
end CON
