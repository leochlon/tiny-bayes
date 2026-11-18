import FarmGroup24
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group24_binding : FarmGroup24Cells = (expectedPart048 ++ expectedPart049) := by
  decide +kernel
theorem group24_expected_valid : ValidCells (expectedPart048 ++ expectedPart049) := by
  rw [← group24_binding]
  exact FarmGroup24Valid
#check group24_expected_valid
#print axioms group24_binding
#print axioms group24_expected_valid
end PinnCertFarm
