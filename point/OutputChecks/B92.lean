import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block92_checked : centerBlock 92 = true := by decide +kernel
#print axioms block92_checked
end PythiaCert.Output
