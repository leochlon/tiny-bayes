import FarmGroup22
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group22_binding : FarmGroup22Cells = (expectedPart044 ++ expectedPart045) := by
  decide +kernel
theorem group22_expected_valid : ValidCells (expectedPart044 ++ expectedPart045) := by
  rw [← group22_binding]
  exact FarmGroup22Valid
#check group22_expected_valid
#print axioms group22_binding
#print axioms group22_expected_valid
end PinnCertFarm
