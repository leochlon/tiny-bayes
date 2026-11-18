import FarmGroup11
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group11_binding : FarmGroup11Cells = (expectedPart022 ++ expectedPart023) := by
  decide +kernel
theorem group11_expected_valid : ValidCells (expectedPart022 ++ expectedPart023) := by
  rw [← group11_binding]
  exact FarmGroup11Valid
#check group11_expected_valid
#print axioms group11_binding
#print axioms group11_expected_valid
end PinnCertFarm
