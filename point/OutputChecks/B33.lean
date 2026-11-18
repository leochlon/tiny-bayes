import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block33_checked : centerBlock 33 = true := by decide +kernel
#print axioms block33_checked
end PythiaCert.Output
