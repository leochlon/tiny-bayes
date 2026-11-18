import Input
import PRO.Checks
import PointData.L0.P14
namespace PythiaCert.Point.L0P14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem h_check : PRO.hCheck (PRO.LL 0) x h = true := by decide +kernel
#print axioms h_check
end PythiaCert.Point.L0P14
