import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding0 : out0 = PinnCert.normalizedResidual := by
  decide +kernel
#print axioms binding0
end PinnStaged
