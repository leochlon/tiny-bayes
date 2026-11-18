import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block186_checked : centerBlock 186 = true := by decide +kernel
#print axioms block186_checked
end PythiaCert.Output
