import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block58_checked : centerBlock 58 = true := by decide +kernel
#print axioms block58_checked
end PythiaCert.Output
