import CON.K.BosBoxes
import CON.K.BosH1

/-! Kernel check for layer 3 on the prompt `[0]`: GELU outputs.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g3 : hidCheck z3 B3 H3 = true := by decide +kernel
end Bos
end CON
