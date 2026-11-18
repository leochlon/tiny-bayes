import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block122_checked : centerBlock 122 = true := by decide +kernel
#print axioms block122_checked
end PythiaCert.Output
