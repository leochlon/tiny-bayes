import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block90_checked : centerBlock 90 = true := by decide +kernel
#print axioms block90_checked
end PythiaCert.Output
