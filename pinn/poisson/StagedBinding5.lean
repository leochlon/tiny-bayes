import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding5 : out5 = PinnCert.residualDy.ndiff false := by
  decide +kernel
#print axioms binding5
end PinnStaged
