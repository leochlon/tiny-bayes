import FarmGroup13
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group13_binding : FarmGroup13Cells = (expectedPart026 ++ expectedPart027) := by
  decide +kernel
theorem group13_expected_valid : ValidCells (expectedPart026 ++ expectedPart027) := by
  rw [← group13_binding]
  exact FarmGroup13Valid
#check group13_expected_valid
#print axioms group13_binding
#print axioms group13_expected_valid
end PinnCertFarm
