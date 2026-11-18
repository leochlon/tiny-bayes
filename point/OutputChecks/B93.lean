import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block93_checked : centerBlock 93 = true := by decide +kernel
#print axioms block93_checked
end PythiaCert.Output
