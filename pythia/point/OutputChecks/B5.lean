import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block5_checked : centerBlock 5 = true := by decide +kernel
#print axioms block5_checked
end PythiaCert.Output
