import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block19_checked : centerBlock 19 = true := by decide +kernel
#print axioms block19_checked
end PythiaCert.Output
