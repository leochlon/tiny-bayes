import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block8_checked : centerBlock 8 = true := by decide +kernel
#print axioms block8_checked
end PythiaCert.Output
