import FarmGroup20
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group20_binding : FarmGroup20Cells = (expectedPart040 ++ expectedPart041) := by
  decide +kernel
theorem group20_expected_valid : ValidCells (expectedPart040 ++ expectedPart041) := by
  rw [← group20_binding]
  exact FarmGroup20Valid
#check group20_expected_valid
#print axioms group20_binding
#print axioms group20_expected_valid
end PinnCertFarm
