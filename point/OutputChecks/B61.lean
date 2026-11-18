import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block61_checked : centerBlock 61 = true := by decide +kernel
#print axioms block61_checked
end PythiaCert.Output
