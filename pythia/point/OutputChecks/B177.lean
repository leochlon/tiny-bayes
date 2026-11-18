import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block177_checked : centerBlock 177 = true := by decide +kernel
#print axioms block177_checked
end PythiaCert.Output
