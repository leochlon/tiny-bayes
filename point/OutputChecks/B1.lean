import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block1_checked : centerBlock 1 = true := by decide +kernel
#print axioms block1_checked
end PythiaCert.Output
