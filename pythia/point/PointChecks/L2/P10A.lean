import Input
import PRO.Checks
import PointData.L2.P0
import PointData.L2.P1
import PointData.L2.P2
import PointData.L2.P3
import PointData.L2.P4
import PointData.L2.P5
import PointData.L2.P6
import PointData.L2.P7
import PointData.L2.P8
import PointData.L2.P9
import PointData.L2.P10
namespace PythiaCert.Point.L2P10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 2) 10 [PythiaCert.Point.L2P0.q, PythiaCert.Point.L2P1.q, PythiaCert.Point.L2P2.q, PythiaCert.Point.L2P3.q, PythiaCert.Point.L2P4.q, PythiaCert.Point.L2P5.q, PythiaCert.Point.L2P6.q, PythiaCert.Point.L2P7.q, PythiaCert.Point.L2P8.q, PythiaCert.Point.L2P9.q, PythiaCert.Point.L2P10.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L2P10
