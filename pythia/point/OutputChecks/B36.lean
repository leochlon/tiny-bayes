import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block36_checked : centerBlock 36 = true := by decide +kernel
#print axioms block36_checked
end PythiaCert.Output
