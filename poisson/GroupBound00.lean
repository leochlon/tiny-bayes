import FarmGroup00
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group00_binding : FarmGroup00Cells = (expectedPart000 ++ expectedPart001) := by
  decide +kernel
theorem group00_expected_valid : ValidCells (expectedPart000 ++ expectedPart001) := by
  rw [← group00_binding]
  exact FarmGroup00Valid
#check group00_expected_valid
#print axioms group00_binding
#print axioms group00_expected_valid
end PinnCertFarm
