import Input
import PRO.Checks
import PointData.L1.P24
namespace PythiaCert.Point.L1P24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem q_check : PRO.qCheck (PRO.LL 1) x q = true := by decide +kernel
#print axioms q_check
end PythiaCert.Point.L1P24
