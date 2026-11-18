import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding4 : out4 = PinnCert.residualDx.ndiff true := by
  decide +kernel
#print axioms binding4
end PinnStaged
