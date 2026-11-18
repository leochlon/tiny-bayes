import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block76_checked : centerBlock 76 = true := by decide +kernel
#print axioms block76_checked
end PythiaCert.Output
