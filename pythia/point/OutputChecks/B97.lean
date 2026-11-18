import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block97_checked : centerBlock 97 = true := by decide +kernel
#print axioms block97_checked
end PythiaCert.Output
