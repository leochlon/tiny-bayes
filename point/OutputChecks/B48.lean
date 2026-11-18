import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block48_checked : centerBlock 48 = true := by decide +kernel
#print axioms block48_checked
end PythiaCert.Output
