import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block66_checked : centerBlock 66 = true := by decide +kernel
#print axioms block66_checked
end PythiaCert.Output
