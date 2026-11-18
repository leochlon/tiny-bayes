import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block30_checked : centerBlock 30 = true := by decide +kernel
#print axioms block30_checked
end PythiaCert.Output
