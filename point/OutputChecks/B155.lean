import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block155_checked : centerBlock 155 = true := by decide +kernel
#print axioms block155_checked
end PythiaCert.Output
