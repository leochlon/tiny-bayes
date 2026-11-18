import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block196_checked : centerBlock 196 = true := by decide +kernel
#print axioms block196_checked
end PythiaCert.Output
