import Input
import PRO.Checks
import PointData.L5.P32
namespace PythiaCert.Point.L5P32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 5) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L5P32
