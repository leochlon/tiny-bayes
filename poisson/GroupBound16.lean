import FarmGroup16
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group16_binding : FarmGroup16Cells = (expectedPart032 ++ expectedPart033) := by
  decide +kernel
theorem group16_expected_valid : ValidCells (expectedPart032 ++ expectedPart033) := by
  rw [← group16_binding]
  exact FarmGroup16Valid
#check group16_expected_valid
#print axioms group16_binding
#print axioms group16_expected_valid
end PinnCertFarm
