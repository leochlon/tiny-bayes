import FarmGroup18
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group18_binding : FarmGroup18Cells = (expectedPart036 ++ expectedPart037) := by
  decide +kernel
theorem group18_expected_valid : ValidCells (expectedPart036 ++ expectedPart037) := by
  rw [← group18_binding]
  exact FarmGroup18Valid
#check group18_expected_valid
#print axioms group18_binding
#print axioms group18_expected_valid
end PinnCertFarm
