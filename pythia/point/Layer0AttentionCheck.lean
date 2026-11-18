import Input
import Layer0Data
import PRO.Checks
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem layer0_31_attention_check : PRO.aCheck (PRO.LL 0) 31 layer0_q Point.L0P31.a = true := by decide +kernel
#print axioms layer0_31_attention_check
end PythiaCert
