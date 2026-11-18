import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block140_checked : centerBlock 140 = true := by decide +kernel
#print axioms block140_checked
end PythiaCert.Output
