import Input
import PRO.Checks
import PointData.L3.P0
import PointData.L3.P1
namespace PythiaCert.Point.L3P1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 3) 1 [PythiaCert.Point.L3P0.q, PythiaCert.Point.L3P1.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L3P1
