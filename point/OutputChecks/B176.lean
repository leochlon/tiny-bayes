import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block176_checked : centerBlock 176 = true := by decide +kernel
#print axioms block176_checked
end PythiaCert.Output
