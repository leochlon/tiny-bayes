import CON.K.BosBoxes
import CON.K.BosL4

/-! Kernel check for layer 5 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a5 : attCheck z5 B5 A5 = true := by decide +kernel
end Bos
end CON
