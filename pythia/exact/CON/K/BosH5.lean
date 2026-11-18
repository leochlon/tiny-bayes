import CON.K.BosBoxes
import CON.K.BosH3

/-! Kernel check for layer 5 on the prompt `[0]`: GELU outputs.
(The second import only orders the heavy checks into three chains, to bound memory.) -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g5 : hidCheck z5 B5 H5 = true := by decide +kernel
end Bos
end CON
