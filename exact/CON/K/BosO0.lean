import CON.K.BosBoxes
import CON.K.BosH3

/-! Kernel check for layer 0 on the prompt `[0]`: residual sum with the MLP output.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem o0 : outCheck z0 (embI (eRowN 0)) A0 H0 B1 = true := by decide +kernel
end Bos
end CON
