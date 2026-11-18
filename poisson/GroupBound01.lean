import FarmGroup01
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group01_binding : FarmGroup01Cells = (expectedPart002 ++ expectedPart003) := by
  decide +kernel
theorem group01_expected_valid : ValidCells (expectedPart002 ++ expectedPart003) := by
  rw [← group01_binding]
  exact FarmGroup01Valid
#check group01_expected_valid
#print axioms group01_binding
#print axioms group01_expected_valid
end PinnCertFarm
