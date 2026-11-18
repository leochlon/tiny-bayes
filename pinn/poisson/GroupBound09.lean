import FarmGroup09
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group09_binding : FarmGroup09Cells = (expectedPart018 ++ expectedPart019) := by
  decide +kernel
theorem group09_expected_valid : ValidCells (expectedPart018 ++ expectedPart019) := by
  rw [← group09_binding]
  exact FarmGroup09Valid
#check group09_expected_valid
#print axioms group09_binding
#print axioms group09_expected_valid
end PinnCertFarm
