import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding1 : out1 = PinnCert.residualDx := by
  decide +kernel
#print axioms binding1
end PinnStaged
