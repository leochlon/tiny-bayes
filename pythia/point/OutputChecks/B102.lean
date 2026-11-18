import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block102_checked : centerBlock 102 = true := by decide +kernel
#print axioms block102_checked
end PythiaCert.Output
