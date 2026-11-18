import FarmGroup07
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group07_binding : FarmGroup07Cells = (expectedPart014 ++ expectedPart015) := by
  decide +kernel
theorem group07_expected_valid : ValidCells (expectedPart014 ++ expectedPart015) := by
  rw [← group07_binding]
  exact FarmGroup07Valid
#check group07_expected_valid
#print axioms group07_binding
#print axioms group07_expected_valid
end PinnCertFarm
