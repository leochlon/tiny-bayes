import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block113_checked : centerBlock 113 = true := by decide +kernel
#print axioms block113_checked
end PythiaCert.Output
