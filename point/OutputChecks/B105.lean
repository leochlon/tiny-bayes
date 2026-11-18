import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block105_checked : centerBlock 105 = true := by decide +kernel
#print axioms block105_checked
end PythiaCert.Output
