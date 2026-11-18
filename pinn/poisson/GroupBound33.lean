import FarmGroup33
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group33_binding : FarmGroup33Cells = (expectedPart066 ++ expectedPart067) := by
  decide +kernel
theorem group33_expected_valid : ValidCells (expectedPart066 ++ expectedPart067) := by
  rw [← group33_binding]
  exact FarmGroup33Valid
#check group33_expected_valid
#print axioms group33_binding
#print axioms group33_expected_valid
end PinnCertFarm
