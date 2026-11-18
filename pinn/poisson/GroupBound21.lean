import FarmGroup21
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group21_binding : FarmGroup21Cells = (expectedPart042 ++ expectedPart043) := by
  decide +kernel
theorem group21_expected_valid : ValidCells (expectedPart042 ++ expectedPart043) := by
  rw [← group21_binding]
  exact FarmGroup21Valid
#check group21_expected_valid
#print axioms group21_binding
#print axioms group21_expected_valid
end PinnCertFarm
