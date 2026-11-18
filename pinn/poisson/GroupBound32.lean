import FarmGroup32
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group32_binding : FarmGroup32Cells = (expectedPart064 ++ expectedPart065) := by
  decide +kernel
theorem group32_expected_valid : ValidCells (expectedPart064 ++ expectedPart065) := by
  rw [← group32_binding]
  exact FarmGroup32Valid
#check group32_expected_valid
#print axioms group32_binding
#print axioms group32_expected_valid
end PinnCertFarm
