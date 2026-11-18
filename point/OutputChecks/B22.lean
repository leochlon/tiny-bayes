import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block22_checked : centerBlock 22 = true := by decide +kernel
#print axioms block22_checked
end PythiaCert.Output
