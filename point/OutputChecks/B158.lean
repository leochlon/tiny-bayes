import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block158_checked : centerBlock 158 = true := by decide +kernel
#print axioms block158_checked
end PythiaCert.Output
