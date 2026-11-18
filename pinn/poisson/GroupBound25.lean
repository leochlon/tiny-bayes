import FarmGroup25
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group25_binding : FarmGroup25Cells = (expectedPart050 ++ expectedPart051) := by
  decide +kernel
theorem group25_expected_valid : ValidCells (expectedPart050 ++ expectedPart051) := by
  rw [← group25_binding]
  exact FarmGroup25Valid
#check group25_expected_valid
#print axioms group25_binding
#print axioms group25_expected_valid
end PinnCertFarm
