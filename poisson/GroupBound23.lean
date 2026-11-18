import FarmGroup23
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group23_binding : FarmGroup23Cells = (expectedPart046 ++ expectedPart047) := by
  decide +kernel
theorem group23_expected_valid : ValidCells (expectedPart046 ++ expectedPart047) := by
  rw [← group23_binding]
  exact FarmGroup23Valid
#check group23_expected_valid
#print axioms group23_binding
#print axioms group23_expected_valid
end PinnCertFarm
