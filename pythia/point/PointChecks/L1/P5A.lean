import Input
import PRO.Checks
import PointData.L1.P0
import PointData.L1.P1
import PointData.L1.P2
import PointData.L1.P3
import PointData.L1.P4
import PointData.L1.P5
namespace PythiaCert.Point.L1P5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 1) 5 [PythiaCert.Point.L1P0.q, PythiaCert.Point.L1P1.q, PythiaCert.Point.L1P2.q, PythiaCert.Point.L1P3.q, PythiaCert.Point.L1P4.q, PythiaCert.Point.L1P5.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L1P5
