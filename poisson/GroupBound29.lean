import FarmGroup29
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group29_binding : FarmGroup29Cells = (expectedPart058 ++ expectedPart059) := by
  decide +kernel
theorem group29_expected_valid : ValidCells (expectedPart058 ++ expectedPart059) := by
  rw [← group29_binding]
  exact FarmGroup29Valid
#check group29_expected_valid
#print axioms group29_binding
#print axioms group29_expected_valid
end PinnCertFarm
