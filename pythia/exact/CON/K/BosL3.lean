import CON.K.BosBoxes
import CON.K.BosL2

/-! Kernel check for layer 3 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a3 : attCheck z3 B3 A3 = true := by decide +kernel
end Bos
end CON
