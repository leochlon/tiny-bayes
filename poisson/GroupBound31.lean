import FarmGroup31
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group31_binding : FarmGroup31Cells = (expectedPart062 ++ expectedPart063) := by
  decide +kernel
theorem group31_expected_valid : ValidCells (expectedPart062 ++ expectedPart063) := by
  rw [← group31_binding]
  exact FarmGroup31Valid
#check group31_expected_valid
#print axioms group31_binding
#print axioms group31_expected_valid
end PinnCertFarm
