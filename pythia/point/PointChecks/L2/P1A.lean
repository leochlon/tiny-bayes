import Input
import PRO.Checks
import PointData.L2.P0
import PointData.L2.P1
namespace PythiaCert.Point.L2P1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem a_check : PRO.aCheck (PRO.LL 2) 1 [PythiaCert.Point.L2P0.q, PythiaCert.Point.L2P1.q] a = true := by decide +kernel
#print axioms a_check
end PythiaCert.Point.L2P1
