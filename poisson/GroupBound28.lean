import FarmGroup28
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group28_binding : FarmGroup28Cells = (expectedPart056 ++ expectedPart057) := by
  decide +kernel
theorem group28_expected_valid : ValidCells (expectedPart056 ++ expectedPart057) := by
  rw [← group28_binding]
  exact FarmGroup28Valid
#check group28_expected_valid
#print axioms group28_binding
#print axioms group28_expected_valid
end PinnCertFarm
