import CON.K.BosBoxes
import CON.K.BosO3

/-! Kernel check for layer 0 on the prompt `[0]`: attention output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem a0 : attCheck z0 (embI (eRowN 0)) A0 = true := by decide +kernel
end Bos
end CON
