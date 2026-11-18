import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block115_checked : centerBlock 115 = true := by decide +kernel
#print axioms block115_checked
end PythiaCert.Output
