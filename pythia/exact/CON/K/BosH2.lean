import CON.K.BosBoxes
import CON.K.BosH0

/-! Kernel check for layer 2 on the prompt `[0]`: GELU outputs.
(The second import only orders the heavy checks into chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g2 : hidCheck z2 B2 H2 = true := by decide +kernel
end Bos
end CON
