import Input
import Layer0Data
import PRO.Checks
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem layer0_31_output_check : PRO.oCheck (PRO.LL 0) Point.L0P31.x Point.L0P31.a Point.L0P31.h Point.L0P31.o = true := by decide +kernel
#print axioms layer0_31_output_check
end PythiaCert
