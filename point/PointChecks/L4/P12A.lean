import Input
import PRO.Checks
import PointData.L4.P0
import PointData.L4.P1
import PointData.L4.P2
import PointData.L4.P3
import PointData.L4.P4
import PointData.L4.P5
import PointData.L4.P6
import PointData.L4.P7
import PointData.L4.P8
import PointData.L4.P9
import PointData.L4.P10
import PointData.L4.P11
import PointData.L4.P12
namespace PythiaCert.Point.L4P12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 4) 12 [PythiaCert.Point.L4P0.q, PythiaCert.Point.L4P1.q, PythiaCert.Point.L4P2.q, PythiaCert.Point.L4P3.q, PythiaCert.Point.L4P4.q, PythiaCert.Point.L4P5.q, PythiaCert.Point.L4P6.q, PythiaCert.Point.L4P7.q, PythiaCert.Point.L4P8.q, PythiaCert.Point.L4P9.q, PythiaCert.Point.L4P10.q, PythiaCert.Point.L4P11.q, PythiaCert.Point.L4P12.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L4P12
