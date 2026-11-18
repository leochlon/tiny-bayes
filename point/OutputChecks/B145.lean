import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block145_checked : centerBlock 145 = true := by decide +kernel
#print axioms block145_checked
end PythiaCert.Output
