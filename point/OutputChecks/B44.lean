import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block44_checked : centerBlock 44 = true := by decide +kernel
#print axioms block44_checked
end PythiaCert.Output
