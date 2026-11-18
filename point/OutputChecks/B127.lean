import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block127_checked : centerBlock 127 = true := by decide +kernel
#print axioms block127_checked
end PythiaCert.Output
