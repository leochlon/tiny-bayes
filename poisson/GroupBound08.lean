import FarmGroup08
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group08_binding : FarmGroup08Cells = (expectedPart016 ++ expectedPart017) := by
  decide +kernel
theorem group08_expected_valid : ValidCells (expectedPart016 ++ expectedPart017) := by
  rw [← group08_binding]
  exact FarmGroup08Valid
#check group08_expected_valid
#print axioms group08_binding
#print axioms group08_expected_valid
end PinnCertFarm
