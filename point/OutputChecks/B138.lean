import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block138_checked : centerBlock 138 = true := by decide +kernel
#print axioms block138_checked
end PythiaCert.Output
