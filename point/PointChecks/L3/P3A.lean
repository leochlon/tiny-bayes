import Input
import PRO.Checks
import PointData.L3.P0
import PointData.L3.P1
import PointData.L3.P2
import PointData.L3.P3
namespace PythiaCert.Point.L3P3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 3) 3 [PythiaCert.Point.L3P0.q, PythiaCert.Point.L3P1.q, PythiaCert.Point.L3P2.q, PythiaCert.Point.L3P3.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L3P3
