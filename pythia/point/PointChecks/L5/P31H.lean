import Input
import PRO.Checks
import PointData.L5.P31
namespace PythiaCert.Point.L5P31
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem h_check : PRO.hCheck (PRO.LL 5) x h = true := by decide +kernel
#print axioms h_check
end PythiaCert.Point.L5P31
