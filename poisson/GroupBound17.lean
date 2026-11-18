import FarmGroup17
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group17_binding : FarmGroup17Cells = (expectedPart034 ++ expectedPart035) := by
  decide +kernel
theorem group17_expected_valid : ValidCells (expectedPart034 ++ expectedPart035) := by
  rw [← group17_binding]
  exact FarmGroup17Valid
#check group17_expected_valid
#print axioms group17_binding
#print axioms group17_expected_valid
end PinnCertFarm
