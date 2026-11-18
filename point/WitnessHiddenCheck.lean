import Input
import Layer0Data
import PRO.Checks
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_hidden_check : PRO.hCheck (PRO.LL 0) Point.L0P32.x Point.L0P32.h = true := by decide +kernel
#print axioms witness_hidden_check
end PythiaCert
