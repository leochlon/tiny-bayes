import FarmGroup26
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group26_binding : FarmGroup26Cells = (expectedPart052 ++ expectedPart053) := by
  decide +kernel
theorem group26_expected_valid : ValidCells (expectedPart052 ++ expectedPart053) := by
  rw [← group26_binding]
  exact FarmGroup26Valid
#check group26_expected_valid
#print axioms group26_binding
#print axioms group26_expected_valid
end PinnCertFarm
