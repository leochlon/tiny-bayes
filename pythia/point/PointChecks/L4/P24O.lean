import Input
import PRO.Checks
import PointData.L4.P24
namespace PythiaCert.Point.L4P24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 4) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L4P24
