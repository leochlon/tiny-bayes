import Input
import PRO.Checks
import PointData.L2.P32
namespace PythiaCert.Point.L2P32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem h_check : PRO.hCheck (PRO.LL 2) x h = true := by decide +kernel
#print axioms h_check
end PythiaCert.Point.L2P32
