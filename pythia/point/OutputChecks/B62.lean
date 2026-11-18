import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block62_checked : centerBlock 62 = true := by decide +kernel
#print axioms block62_checked
end PythiaCert.Output
