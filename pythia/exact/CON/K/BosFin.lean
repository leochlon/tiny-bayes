import CON.K.BosBoxes
import CON.Cert2

/-! Kernel checks on the prompt `[0]`: final LayerNorm, unembedding rows, two-way probabilities. -/

namespace CON
namespace Bos
set_option maxHeartbeats 0 in
theorem fin_17_18 : probCheck (uRowN 17) (uRowN 18) B6 980688 980689 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem fin_470_337 : probCheck (uRowN 470) (uRowN 337) B6 912424 912426 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem fin_4797_2502 : probCheck (uRowN 4797) (uRowN 2502) B6 407692 407694 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem mass_2502_50 : massCheck (uRowN 2502) (uRowN 50) B6 116 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem mass_4797_50 : massCheck (uRowN 4797) (uRowN 50) B6 168 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem mass_18_50 : massCheck (uRowN 18) (uRowN 50) B6 141285996 = true := by decide +kernel
end Bos
end CON
