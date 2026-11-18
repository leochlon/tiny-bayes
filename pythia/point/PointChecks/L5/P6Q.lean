import Input
import PRO.Checks
import PointData.L5.P6
namespace PythiaCert.Point.L5P6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 5) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L5P6
