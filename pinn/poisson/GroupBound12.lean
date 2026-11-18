import FarmGroup12
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group12_binding : FarmGroup12Cells = (expectedPart024 ++ expectedPart025) := by
  decide +kernel
theorem group12_expected_valid : ValidCells (expectedPart024 ++ expectedPart025) := by
  rw [← group12_binding]
  exact FarmGroup12Valid
#check group12_expected_valid
#print axioms group12_binding
#print axioms group12_expected_valid
end PinnCertFarm
