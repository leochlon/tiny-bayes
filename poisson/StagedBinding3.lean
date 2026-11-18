import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding3 : out3 = PinnCert.residualDx.ndiff false := by
  decide +kernel
#print axioms binding3
end PinnStaged
