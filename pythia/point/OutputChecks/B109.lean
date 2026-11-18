import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block109_checked : centerBlock 109 = true := by decide +kernel
#print axioms block109_checked
end PythiaCert.Output
