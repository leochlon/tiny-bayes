import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block123_checked : centerBlock 123 = true := by decide +kernel
#print axioms block123_checked
end PythiaCert.Output
