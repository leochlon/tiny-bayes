import CON.K.BosBoxes
import CON.K.BosH2

/-! Kernel check for layer 4 on the prompt `[0]`: GELU outputs.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g4 : hidCheck z4 B4 H4 = true := by decide +kernel
end Bos
end CON
