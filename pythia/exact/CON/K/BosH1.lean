import CON.K.BosBoxes

/-! Kernel check for layer 1 on the prompt `[0]`: GELU outputs. -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g1 : hidCheck z1 B1 H1 = true := by decide +kernel
end Bos
end CON
