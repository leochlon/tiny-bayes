import CON.K.BosBoxes
import CON.K.BosL3

/-! Kernel check for layer 4 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a4 : attCheck z4 B4 A4 = true := by decide +kernel
end Bos
end CON
