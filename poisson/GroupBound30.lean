import FarmGroup30
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group30_binding : FarmGroup30Cells = (expectedPart060 ++ expectedPart061) := by
  decide +kernel
theorem group30_expected_valid : ValidCells (expectedPart060 ++ expectedPart061) := by
  rw [← group30_binding]
  exact FarmGroup30Valid
#check group30_expected_valid
#print axioms group30_binding
#print axioms group30_expected_valid
end PinnCertFarm
