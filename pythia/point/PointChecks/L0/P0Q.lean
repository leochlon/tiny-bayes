import Input
import PRO.Compose
import PointData.L0.P0
namespace PythiaCert.Point.L0P0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 0) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L0P0
