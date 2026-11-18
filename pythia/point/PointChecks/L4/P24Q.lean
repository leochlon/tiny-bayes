import Input
import PRO.Checks
import PointData.L4.P24
namespace PythiaCert.Point.L4P24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 4) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L4P24
