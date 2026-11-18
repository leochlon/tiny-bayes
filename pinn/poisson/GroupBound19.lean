import FarmGroup19
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group19_binding : FarmGroup19Cells = (expectedPart038 ++ expectedPart039) := by
  decide +kernel
theorem group19_expected_valid : ValidCells (expectedPart038 ++ expectedPart039) := by
  rw [← group19_binding]
  exact FarmGroup19Valid
#check group19_expected_valid
#print axioms group19_binding
#print axioms group19_expected_valid
end PinnCertFarm
