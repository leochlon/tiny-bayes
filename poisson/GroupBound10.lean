import FarmGroup10
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group10_binding : FarmGroup10Cells = (expectedPart020 ++ expectedPart021) := by
  decide +kernel
theorem group10_expected_valid : ValidCells (expectedPart020 ++ expectedPart021) := by
  rw [← group10_binding]
  exact FarmGroup10Valid
#check group10_expected_valid
#print axioms group10_binding
#print axioms group10_expected_valid
end PinnCertFarm
