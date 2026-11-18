import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block25_checked : centerBlock 25 = true := by decide +kernel
#print axioms block25_checked
end PythiaCert.Output
