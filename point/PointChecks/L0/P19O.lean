import Input
import PRO.Checks
import PointData.L0.P19
namespace PythiaCert.Point.L0P19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 0) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L0P19
