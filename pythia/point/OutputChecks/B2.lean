import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block2_checked : centerBlock 2 = true := by decide +kernel
#print axioms block2_checked
end PythiaCert.Output
