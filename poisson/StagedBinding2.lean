import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding2 : out2 = PinnCert.residualDy := by
  decide +kernel
#print axioms binding2
end PinnStaged
