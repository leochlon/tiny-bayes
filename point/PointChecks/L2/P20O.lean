import Input
import PRO.Checks
import PointData.L2.P20
namespace PythiaCert.Point.L2P20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 2) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L2P20
