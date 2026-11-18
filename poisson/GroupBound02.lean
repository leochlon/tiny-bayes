import FarmGroup02
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group02_binding : FarmGroup02Cells = (expectedPart004 ++ expectedPart005) := by
  decide +kernel
theorem group02_expected_valid : ValidCells (expectedPart004 ++ expectedPart005) := by
  rw [← group02_binding]
  exact FarmGroup02Valid
#check group02_expected_valid
#print axioms group02_binding
#print axioms group02_expected_valid
end PinnCertFarm
