import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block41_checked : centerBlock 41 = true := by decide +kernel
#print axioms block41_checked
end PythiaCert.Output
