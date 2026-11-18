import FarmGroup03
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group03_binding : FarmGroup03Cells = (expectedPart006 ++ expectedPart007) := by
  decide +kernel
theorem group03_expected_valid : ValidCells (expectedPart006 ++ expectedPart007) := by
  rw [← group03_binding]
  exact FarmGroup03Valid
#check group03_expected_valid
#print axioms group03_binding
#print axioms group03_expected_valid
end PinnCertFarm
