import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block37_checked : centerBlock 37 = true := by decide +kernel
#print axioms block37_checked
end PythiaCert.Output
