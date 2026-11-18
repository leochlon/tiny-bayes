import Input
import PRO.Checks
import PointData.L0.P0
import PointData.L0.P1
import PointData.L0.P2
import PointData.L0.P3
namespace PythiaCert.Point.L0P3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 0) 3 [PythiaCert.Point.L0P0.q, PythiaCert.Point.L0P1.q, PythiaCert.Point.L0P2.q, PythiaCert.Point.L0P3.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L0P3
