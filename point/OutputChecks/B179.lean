import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block179_checked : centerBlock 179 = true := by decide +kernel
#print axioms block179_checked
end PythiaCert.Output
