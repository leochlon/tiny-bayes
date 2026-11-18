import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block174_checked : centerBlock 174 = true := by decide +kernel
#print axioms block174_checked
end PythiaCert.Output
