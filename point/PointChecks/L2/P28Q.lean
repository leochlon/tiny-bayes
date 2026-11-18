import Input
import PRO.Checks
import PointData.L2.P28
namespace PythiaCert.Point.L2P28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 2) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L2P28
