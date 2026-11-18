import Input
import PRO.Checks
import PointData.L2.P0
import PointData.L2.P1
import PointData.L2.P2
namespace PythiaCert.Point.L2P2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 2) 2 [PythiaCert.Point.L2P0.q, PythiaCert.Point.L2P1.q, PythiaCert.Point.L2P2.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L2P2
