import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block3_checked : centerBlock 3 = true := by decide +kernel
#print axioms block3_checked
end PythiaCert.Output
