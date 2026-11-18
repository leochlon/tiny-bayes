import CON.K.BosBoxes
import CON.K.BosL0

/-! Kernel check for layer 1 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a1 : attCheck z1 B1 A1 = true := by decide +kernel
end Bos
end CON
