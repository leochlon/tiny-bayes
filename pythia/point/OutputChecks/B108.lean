import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block108_checked : centerBlock 108 = true := by decide +kernel
#print axioms block108_checked
end PythiaCert.Output
