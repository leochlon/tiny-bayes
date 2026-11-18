import StagedExpr
import ResidualData
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
namespace PinnStaged
theorem binding6 : out6 = PinnCert.residualDy.ndiff true := by
  decide +kernel
#print axioms binding6
end PinnStaged
