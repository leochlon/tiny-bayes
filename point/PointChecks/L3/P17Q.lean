import Input
import PRO.Checks
import PointData.L3.P17
namespace PythiaCert.Point.L3P17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 3) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L3P17
