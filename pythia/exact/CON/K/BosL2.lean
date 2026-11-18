import CON.K.BosBoxes
import CON.K.BosL1

/-! Kernel check for layer 2 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a2 : attCheck z2 B2 A2 = true := by decide +kernel
end Bos
end CON
