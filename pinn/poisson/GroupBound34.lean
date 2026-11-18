import FarmGroup34
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group34_binding : FarmGroup34Cells = (expectedPart068 ++ expectedPart069) := by
  decide +kernel
theorem group34_expected_valid : ValidCells (expectedPart068 ++ expectedPart069) := by
  rw [← group34_binding]
  exact FarmGroup34Valid
#check group34_expected_valid
#print axioms group34_binding
#print axioms group34_expected_valid
end PinnCertFarm
