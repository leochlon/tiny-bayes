import Input
import PRO.Checks
import PointData.L0.P0
namespace PythiaCert.Point.L0P0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 0) 0 [PythiaCert.Point.L0P0.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L0P0
