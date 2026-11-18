import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block56_checked : centerBlock 56 = true := by decide +kernel
#print axioms block56_checked
end PythiaCert.Output
