import FarmGroup05
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group05_binding : FarmGroup05Cells = (expectedPart010 ++ expectedPart011) := by
  decide +kernel
theorem group05_expected_valid : ValidCells (expectedPart010 ++ expectedPart011) := by
  rw [← group05_binding]
  exact FarmGroup05Valid
#check group05_expected_valid
#print axioms group05_binding
#print axioms group05_expected_valid
end PinnCertFarm
