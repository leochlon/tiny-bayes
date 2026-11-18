import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block133_checked : centerBlock 133 = true := by decide +kernel
#print axioms block133_checked
end PythiaCert.Output
