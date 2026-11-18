import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block0_checked : centerBlock 0 = true := by decide +kernel
#print axioms block0_checked
end PythiaCert.Output
