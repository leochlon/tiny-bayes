import Input
import PRO.Checks
import PointData.L3.P0
import PointData.L3.P1
import PointData.L3.P2
import PointData.L3.P3
import PointData.L3.P4
import PointData.L3.P5
import PointData.L3.P6
import PointData.L3.P7
import PointData.L3.P8
import PointData.L3.P9
import PointData.L3.P10
import PointData.L3.P11
import PointData.L3.P12
import PointData.L3.P13
import PointData.L3.P14
import PointData.L3.P15
namespace PythiaCert.Point.L3P15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 3) 15 [PythiaCert.Point.L3P0.q, PythiaCert.Point.L3P1.q, PythiaCert.Point.L3P2.q, PythiaCert.Point.L3P3.q, PythiaCert.Point.L3P4.q, PythiaCert.Point.L3P5.q, PythiaCert.Point.L3P6.q, PythiaCert.Point.L3P7.q, PythiaCert.Point.L3P8.q, PythiaCert.Point.L3P9.q, PythiaCert.Point.L3P10.q, PythiaCert.Point.L3P11.q, PythiaCert.Point.L3P12.q, PythiaCert.Point.L3P13.q, PythiaCert.Point.L3P14.q, PythiaCert.Point.L3P15.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L3P15
