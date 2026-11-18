import Input
import PRO.Checks
import PointData.L3.P25
namespace PythiaCert.Point.L3P25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 3) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L3P25
