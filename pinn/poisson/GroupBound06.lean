import FarmGroup06
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group06_binding : FarmGroup06Cells = (expectedPart012 ++ expectedPart013) := by
  decide +kernel
theorem group06_expected_valid : ValidCells (expectedPart012 ++ expectedPart013) := by
  rw [← group06_binding]
  exact FarmGroup06Valid
#check group06_expected_valid
#print axioms group06_binding
#print axioms group06_expected_valid
end PinnCertFarm
