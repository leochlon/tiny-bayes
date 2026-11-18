import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block183_checked : centerBlock 183 = true := by decide +kernel
#print axioms block183_checked
end PythiaCert.Output
