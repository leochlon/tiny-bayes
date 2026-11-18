import Input
import Layer0Data
import PRO.Checks
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_output_check : PRO.oCheck (PRO.LL 0) Point.L0P32.x Point.L0P32.a Point.L0P32.h Point.L0P32.o = true := by decide +kernel
#print axioms witness_output_check
end PythiaCert
