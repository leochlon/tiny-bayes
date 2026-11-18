import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block32_checked : centerBlock 32 = true := by decide +kernel
#print axioms block32_checked
end PythiaCert.Output
