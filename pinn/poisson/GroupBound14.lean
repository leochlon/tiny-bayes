import FarmGroup14
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group14_binding : FarmGroup14Cells = (expectedPart028 ++ expectedPart029) := by
  decide +kernel
theorem group14_expected_valid : ValidCells (expectedPart028 ++ expectedPart029) := by
  rw [← group14_binding]
  exact FarmGroup14Valid
#check group14_expected_valid
#print axioms group14_binding
#print axioms group14_expected_valid
end PinnCertFarm
