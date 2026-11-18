import Input
import PRO.Checks
import PointData.L0.P0
import PointData.L0.P1
import PointData.L0.P2
import PointData.L0.P3
import PointData.L0.P4
import PointData.L0.P5
import PointData.L0.P6
import PointData.L0.P7
import PointData.L0.P8
import PointData.L0.P9
import PointData.L0.P10
import PointData.L0.P11
import PointData.L0.P12
namespace PythiaCert.Point.L0P12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 0) 12 [PythiaCert.Point.L0P0.q, PythiaCert.Point.L0P1.q, PythiaCert.Point.L0P2.q, PythiaCert.Point.L0P3.q, PythiaCert.Point.L0P4.q, PythiaCert.Point.L0P5.q, PythiaCert.Point.L0P6.q, PythiaCert.Point.L0P7.q, PythiaCert.Point.L0P8.q, PythiaCert.Point.L0P9.q, PythiaCert.Point.L0P10.q, PythiaCert.Point.L0P11.q, PythiaCert.Point.L0P12.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L0P12
