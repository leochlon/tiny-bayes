import FarmGroup35
import CoverBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnCertFarm
theorem group35_binding : FarmGroup35Cells = (expectedPart070 ++ expectedPart071) := by
  decide +kernel
theorem group35_expected_valid : ValidCells (expectedPart070 ++ expectedPart071) := by
  rw [← group35_binding]
  exact FarmGroup35Valid
#check group35_expected_valid
#print axioms group35_binding
#print axioms group35_expected_valid
end PinnCertFarm
