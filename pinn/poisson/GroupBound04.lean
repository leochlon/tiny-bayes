import FarmGroup04
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group04_binding : FarmGroup04Cells = (expectedPart008 ++ expectedPart009) := by
  decide +kernel
theorem group04_expected_valid : ValidCells (expectedPart008 ++ expectedPart009) := by
  rw [← group04_binding]
  exact FarmGroup04Valid
#check group04_expected_valid
#print axioms group04_binding
#print axioms group04_expected_valid
end PinnCertFarm
