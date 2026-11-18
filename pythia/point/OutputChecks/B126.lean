import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block126_checked : centerBlock 126 = true := by decide +kernel
#print axioms block126_checked
end PythiaCert.Output
