import Input
import Layer0Data
import PRO.Checks
namespace PythiaCert
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_attention_check : PRO.aCheck (PRO.LL 0) 31 (layer0_q.take 31 ++ [Point.L0P32.q]) Point.L0P32.a = true := by decide +kernel
#print axioms witness_attention_check
end PythiaCert
