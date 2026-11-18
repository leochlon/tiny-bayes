import FarmGroup15
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group15_binding : FarmGroup15Cells = (expectedPart030 ++ expectedPart031) := by
  decide +kernel
theorem group15_expected_valid : ValidCells (expectedPart030 ++ expectedPart031) := by
  rw [← group15_binding]
  exact FarmGroup15Valid
#check group15_expected_valid
#print axioms group15_binding
#print axioms group15_expected_valid
end PinnCertFarm
