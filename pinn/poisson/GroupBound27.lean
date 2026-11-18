import FarmGroup27
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group27_binding : FarmGroup27Cells = (expectedPart054 ++ expectedPart055) := by
  decide +kernel
theorem group27_expected_valid : ValidCells (expectedPart054 ++ expectedPart055) := by
  rw [← group27_binding]
  exact FarmGroup27Valid
#check group27_expected_valid
#print axioms group27_binding
#print axioms group27_expected_valid
end PinnCertFarm
