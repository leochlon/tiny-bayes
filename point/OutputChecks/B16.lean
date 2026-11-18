import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block16_checked : centerBlock 16 = true := by decide +kernel
#print axioms block16_checked
end PythiaCert.Output
