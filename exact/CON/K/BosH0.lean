import CON.K.BosBoxes

/-! Kernel check for layer 0 on the prompt `[0]`: GELU outputs. -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem g0 : hidCheck z0 (embI (eRowN 0)) H0 = true := by decide +kernel
end Bos
end CON
