import Input
import PRO.Checks
import PointData.L1.P15
namespace PythiaCert.Point.L1P15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem o_check : PRO.oCheck (PRO.LL 1) x a h o = true := by decide +kernel
#print axioms o_check
end PythiaCert.Point.L1P15
