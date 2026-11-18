import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block192_checked : centerBlock 192 = true := by decide +kernel
#print axioms block192_checked
end PythiaCert.Output
